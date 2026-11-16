-- Prove2me | Theorems.Thm_GuardedSSSP_Supplement_theorem_E_3
-- name    : GuardedSSSP.Supplement.theorem_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:23:06.953616+00:00
-- url     : https://prove2.me/theorems/e3b0dc8a-dad2-470b-9eec-88efaec0934f
-- title:
--   Theorem E.3, p.40 — exact cyclic composition: the phase algorithm computes $z_\beta(v)=d_\beta(v)+S-p(v)$
-- statement:
--   Let $H=(V,E)$ be a finite directed multigraph with nonnegative real weights $w$ and a root $r$ reaching every vertex. Let $p(v)=\mathrm{dist}_H(r,v)$ be the exact calibration, $S=\max_v p(v)$, and let $\beta:V\to[0,\infty]$ be any seed vector ($\infty$ = absent). Let $D$ be any rooted tree on $V$ with root $r$ that is single-entry for $H$ (Definition D.1), and process the vertices of $D$ in any child-before-parent order with the phase algorithm of Appendix E.1. Then its output (54) satisfies
--
--   $$z(v)=z_\beta(v)=d_\beta(v)+S-p(v)\qquad\text{for every }v\in V,$$
--
--   where $d_\beta(v)=\min_x\{\beta(x)+\mathrm{dist}_H(x,v)\}$ is the seeded distance (44). Both sides are $\infty$ exactly when no present seed reaches $v$. Ties, zero weights and zero-cost cycles are allowed.
--
--   This exactness is what lets Theorem C.1 answer seeded queries by composing local quotient computations: cyclic interactions between sibling regions are resolved once per parent, and an improved ancestor value reaches a finished region only through a minimum.
--
--   **Formalization Note** The phase algorithm, residuals and quotients are those of `GuardedSSSP.Supplement.phaseOutput`; the tree need not be the dominator tree.
--
--   Differences from the source:
--   - reading: the phase algorithm (steps 1–5 of Appendix E.1, run with a path-minima structure and a quotient solver) → a Lean function on EReal labels (phaseOutput): steps 1–3 at each vertex in the processing order, then (54); step 4 changes no value; reason: Theorem E.3 is a statement about the computed values; the data structures of Appendices F and G only compute these values
--   - reading: child-before-parent phase order → every bijection ord : Fin n ≃ Fin n in which each non-root vertex precedes its parent; reason: the paper allows any such order
--   - encoding: any exact auxiliary calibration → p = dist_H(r, ·) for the tree's root r, with r reaching every vertex (dist_H(r, v) ≠ ⊤); reason: Appendix D defines the calibration as p(v) = dist_H(r, v); the Appendix C assumption that r reaches every vertex makes it finite
--   - encoding: held nonnegative seed vector β(v) ∈ [0, ∞] → β : Fin n → EReal with 0 ≤ β v, ⊤ for an absent seed; reason: same values; ∞ is ⊤
--   - encoding: a rooted tree D on V with root r → a parent map par with par r = r such that every vertex reaches r by iterating par; reason: the standard encoding of a rooted tree; the root's parent slot points to itself
--   - encoding: solve seeded shortest paths on Q_g once and replace every child cap q(a) by the resulting quotient distance → q(a) := infimum over children b and quotient walks P from b to a of seed(b) + Σ_{e∈P} c_e; reason: the paper's local solver computes actual shortest-path minima from the held seeds
--   - encoding: step 3 uses the residual R_e and the step-2 cap q(a) → the residual is evaluated on the labels after step 2; reason: R_e involves only proper descendants of a, which step 2 does not change
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Theorem E.3, p.40 (PDF p.41); Appendix E.1, (52)–(54), p.39 (PDF p.40); Definition D.1, (48)–(50), p.38 (PDF p.39)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_Supplement_seededDist
import Definitions.Def_GuardedSSSP_Supplement_RootedTree
import Definitions.Def_GuardedSSSP_Supplement_phaseOutput

namespace GuardedSSSP

namespace Supplement

open AtomicDynRouting.ResidenceTime

/-- **Theorem E.3** (Exact cyclic composition).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), Theorem E.3, p.40 (PDF p.41); the phase algorithm of
Appendix E.1, (52)–(54), p.39 (PDF p.40); Definition D.1 and (48)–(50), p.38 (PDF p.39); (44), p.36.

"The phase algorithm computes z(v) = z_β(v) for every vertex, for any single-entry tree, any exact auxiliary
calibration, and any held nonnegative seed vector."

For a finite directed multigraph `G` with weights `w ≥ 0`, a root `r` reaching every vertex, any rooted
tree `par` on the vertices with root `r` that is single-entry for `G` (Definition D.1), any
child-before-parent processing order `ord`, and any seed vector `β` with values in `[0, ∞]`, the output
(54) of the phase algorithm equals `z_β(v) = d_β(v) + S − p(v)` (50) at every vertex `v`, where
`p = dist_G(r, ·)` and `S = max_v p(v)`.

**Formalization Note.**
* The phase algorithm, the residuals, the quotients and the calibration are the definitions of
  `GuardedSSSP.Supplement.phaseOutput`; the algorithm is a function on values, not a RAM program.
* "Any exact auxiliary calibration": the calibration is `p = dist_G(r, ·)` for the tree's root `r`; the
  hypothesis that `r` reaches every vertex makes it finite.
* Seeds are `β : Fin n → EReal` with `0 ≤ β v`; `β v = ⊤` is an absent seed. `d_β` and `z_β` are `⊤`
  where no present seed reaches `v`, and so is the algorithm's output (the same tagged-minimum
  convention).
* Weights may be zero; ties, parallel arcs, loops and zero-cost cycles are allowed. -/
theorem theorem_E_3 {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (hw : ∀ e, 0 ≤ w e)
    (r : Fin n) (hr : ∀ v, dist G w r v ≠ ⊤) (par : Fin n → Fin n) (hD : IsRootedTree par r)
    (hSE : IsSingleEntry G par r) (ord : Fin n ≃ Fin n) (hord : IsChildBeforeParent par r ord)
    (β : Fin n → EReal) (hβ : ∀ v, 0 ≤ β v) :
    ∀ v : Fin n, phaseOutput G w par r ord β v = zTarget G w r β v := by sorry

end Supplement

end GuardedSSSP
