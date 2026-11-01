-- Prove2me | Theorems.Thm_MVBlossoms_lemma_20
-- name    : MVBlossoms.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:46:06.35161+00:00
-- url     : https://prove2.me/theorems/74fb263b-f240-44ef-b2d0-a4ee208f3e94
-- title:
--   Lemma 20 — iterated bases of a vertex on a shortest even path lie on it, inside nested blossoms
-- statement:
--   Let $t$ be an eligible tenacity and $p$ an even level($v$) path from an unmatched vertex $f$. Let $u$ lie on $p$ with $\mathrm{tenacity}(u)\le t$, let $l=k(t+2,u)$, and let $x_i=\mathrm{base}^i(u)$ and $s_i=\mathrm{tenacity}(x_i)$ for $1\le i\le l$. Then these iterated bases exist, and
--
--   1. $x_1,\dots,x_l$ all lie on $p$; and
--   2. for $1\le i\le l$, every vertex of $p[x_i\text{ to }u]$ lies in $\{x_i\}\cup B_{x_i,\min(s_i-2,\,t)}$.
--
--   For $i<l$ one has $s_i\le t$ and the blossom is $B_{x_i,s_i-2}$, as printed.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The hypothesis that $t$ is eligible implies $t_m<l_m$.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: b = base(v), the unique element of B(v) (Definitions 21, 29) → the relation IsBase M (x i) (x (i + 1)), i.e. baseSet M (x i) = {x (i + 1)}, in the chain of IsKIndex; reason: no junk value for base(v); together with Statement 2 / Corollary 2 it is the printed claim
--   - encoding: B_{b,t} by Definitions 22 and 31, union over basal v → one recursion blossom M b t on t, union over all w ∈ T_{b,t} ∪ {b}; reason: a non-basal w has an empty blossom, so the union is unchanged; at t = t_m it is Definition 22
--   - encoding: p[b to u], b before or after u on p (Definitions 7, 24, 33) → some q : G.Walk b u with IsSegmentFrom p q (p = p₁ q p₂ or p = p₁ q⁻¹ p₂); reason: on a simple path the segment exists and is unique when b, u lie on p
--   - reading: B_{x_i, s_i − 2}, the blossom of tenacity s_i − 2 with base x_i → blossom M (x i) (min (s_i − 2) t), computed in ℕ∞; reason: for i < l it is the printed blossom; for i = l the printed blossom is undefined when s_l = ∞ or s_l − 2 ≥ l_m (Definition 31 covers eligible tenacities only); where it is defined it contains B_{x_l,t}, so the Lean reading is the stronger one; the proof of Lemma 16 uses it at the stage's tenacity
--   - encoding: "let the iterated bases of u ... be x1, ..., xl" (presupposed to exist) → the existence of the chain x with l = k(t + 2, u) is a conclusion; parts 1 and 2 hold for every such chain; reason: states the presupposition explicitly; the chain is unique since IsBase is functional
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 20, p.2039

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_IsEligible
import Definitions.Def_MVBlossoms_IsKIndex
import Definitions.Def_MVBlossoms_IsSegmentFrom
import Definitions.Def_MVBlossoms_blossom

namespace MVBlossoms

/-- **Lemma 20 (reading: blossom of tenacity min(s_i − 2, t)).** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 20, p.2039:
"Let p be an even level(v) path from unmatched vertex f to an arbitrary vertex v. Let vertex u ∈ p
with tenacity(u) ≤ t, and let l = k(t + 2,u). Let the iterated bases of u, base¹(u), …, base^l(u), be
x1, …, xl, respectively. For 1 ≤ i ≤ l, let si = tenacity(xi), and let B_{xi,si−2} be the blossom of
tenacity si − 2 with base xi. Then, 1. the iterated bases of u, x1, …, xl, lie on p; and 2. for
1 ≤ i ≤ l, the path p[xi to u] lies in {xi} ∪ B_{xi,si−2}."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). `t` is an eligible tenacity. The conclusion first records that the
chain of iterated bases `x 0 = u, x 1, …, x l` with `l = k(t + 2, u)` exists (`IsKIndex`), then
proves parts 1 and 2 for every such chain. The blossom in part 2 is `B_{x_i, min(s_i − 2, t)}`: for
`i < l` this is the printed `B_{x_i, s_i − 2}`; for `i = l` the printed blossom is undefined when
`s_l = ∞` or `s_l − 2 ≥ l_m`, and where it is defined it contains `B_{x_l, t}`. The index
`(min (s_i − 2) t).toNat` is computed in `ℕ∞` and is at most `t`, so `toNat` is never applied to
`⊤`. -/
theorem lemma_20 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching)
    (t : ℕ) (ht : IsEligible M t)
    {f v : V} (p : G.Walk f v) (hp : IsEvenLevelPath M p)
    (u : V) (hu : u ∈ p.support) (hten : tenacity M u ≤ (t : ℕ∞)) :
    (∃ (x : ℕ → V) (l : ℕ), IsKIndex M (t + 2) u x l) ∧
    ∀ (x : ℕ → V) (l : ℕ), IsKIndex M (t + 2) u x l →
      (∀ i, 1 ≤ i → i ≤ l → x i ∈ p.support) ∧
      (∀ i, 1 ≤ i → i ≤ l → ∃ q : G.Walk (x i) u, IsSegmentFrom p q ∧
        ∀ y ∈ q.support, y = x i ∨
          y ∈ blossom M (x i) (min (tenacity M (x i) - 2) (t : ℕ∞)).toNat) := by sorry

end MVBlossoms
