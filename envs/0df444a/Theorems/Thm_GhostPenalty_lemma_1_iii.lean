-- Prove2me | Theorems.Thm_GhostPenalty_lemma_1_iii
-- name    : GhostPenalty.lemma_1_iii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:56.368212+00:00
-- url     : https://prove2.me/theorems/bf438639-5815-4285-90c8-f58d7e6a1d8e
-- title:
--   Lemma 1 (iii) — $(d,x)\mapsto N_{\beta\mathbb B^n_\infty\cap(K-x)}(d)$ is outer semicontinuous on $C$
-- statement:
--   Let $K\subseteq\mathbb R^n$ be nonempty, closed and convex and $\beta>0$. With
--   $$C\triangleq\{(d,x)\in\beta\mathbb B^n_\infty\times K:\ d+x\in K\},$$
--   the set-valued map $(d,x)\mapsto N_{\beta\mathbb B^n_\infty\cap(K-x)}(d)$ is outer semicontinuous on $C$ relative to $C$: if $(d^\nu,x^\nu)\to(\bar d,\bar x)$ in $C$, $\eta^\nu\in N_{\beta\mathbb B^n_\infty\cap(K-x^\nu)}(d^\nu)$ and $\eta^\nu\to\bar\eta$, then $\bar\eta\in N_{\beta\mathbb B^n_\infty\cap(K-\bar x)}(\bar d)$.
--
--   This is what allows passing to the limit in the subproblem KKT conditions (18).
--
--   Differences from the source:
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
--   - encoding: outer semicontinuity of a set-valued mapping (Rockafellar–Wets) → OuterSemicontWithinAt, the sequential form, at every point of C; reason: the sequential form is Rockafellar–Wets' definition in ℝⁿ
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Lemma 1 (iii), p.9

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_GhostPenalty_box
import Definitions.Def_GhostPenalty_OuterSemicontWithinAt
open FirstOrderOpt.ConvexTheory

namespace GhostPenalty

/-- **Lemma 1 (iii): outer semicontinuity of `(d, x) ↦ N_{βBⁿ∞∩(K−x)}(d)` on `C`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Lemma 1 (iii), p.9: "letting `C ≜ {(d,x) ∈ βBⁿ∞ × K : d + x ∈ K}`, the set-valued
mapping `N_{βBⁿ∞∩(K−•)}(•)` is outer semicontinuous on `C` relative to `C`."

**Formalization Note.** `K` is nonempty, closed and convex (blanket assumption) and `β > 0`
(the paper's user-chosen positive constant). Pairs `(d, x)` are elements of `ℝⁿ × ℝⁿ`; the
mapping sends `(d, x)` to the published `normalCone` of `box n β ∩ {u | x + u ∈ K}` at `d`, which
on `C` is a point of that set. Outer semicontinuity is the sequential `OuterSemicontWithinAt`,
required at every point of `C`. -/
theorem lemma_1_iii {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (β : ℝ) (hβ : 0 < β) :
    ∀ p ∈ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        q.1 ∈ box n β ∧ q.2 ∈ K ∧ q.1 + q.2 ∈ K},
      OuterSemicontWithinAt
        (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          normalCone (box n β ∩ {u | q.2 + u ∈ K}) q.1)
        {q | q.1 ∈ box n β ∧ q.2 ∈ K ∧ q.1 + q.2 ∈ K} p := by sorry

end GhostPenalty
