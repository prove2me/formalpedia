-- Prove2me | Theorems.Thm_MinVolEllipsoid_P_eq_cone_slice
-- name    : MinVolEllipsoid.P_eq_cone_slice
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:34.129643+00:00
-- url     : https://prove2.me/theorems/62554b64-89fd-4d5f-a7d4-67758ca21876
-- title:
--   Proof of Theorem 1, p.8: $\mathcal P=\{x\in\mathbb R^K:[x;1]\in\mathcal K\}$
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). Then
--
--   $$
--   \mathcal P=\{x\in\mathbb R^K:\ [x;1]\in\mathcal K\}.
--   $$
--
--   This identification lets the paper rewrite the supremum (1) over $\mathcal P$ as the supremum (6) over the slice $\{[x;1]\in\mathcal K\}$ of the cone, the first step of the proof of Theorem 1.
--
--   Differences from the source:
--
--   - encoding: vectors [x; τ] ∈ ℝ^{K+1} with τ the last coordinate → Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ, τ at the Unit coordinate; reason: Lean convention for ℝ^{K+1}; same vectors
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, proof of Theorem 1, p.8, "The set P can be expressed in terms of the cone K as P = {x ∈ R^K : [x; 1] ∈ K}"

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone

namespace MinVolEllipsoid

/-- **`𝒫 = {x ∈ ℝᴷ : [x; 1] ∈ 𝒦}`** (Mittal & Hanasusanto, arXiv:1807.07507v4, proof of
Theorem 1, p.8, "The set 𝒫 can be expressed in terms of the cone 𝒦 as
𝒫 = {x ∈ ℝᴷ : [x; 1] ∈ 𝒦}").

For `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1) and `𝒦 = liftCone P` as in (2), `P` is exactly the
set of `x` whose lift `[x; 1]` lies in `𝒦`.

**Formalization Note** `[x; 1]` is `MinVolEllipsoid.lift x`, the `Unit` coordinate being the
paper's last coordinate. -/
theorem P_eq_cone_slice {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) :
    P = {x : Fin n → ℝ | lift x ∈ liftCone P} := by sorry

end MinVolEllipsoid
