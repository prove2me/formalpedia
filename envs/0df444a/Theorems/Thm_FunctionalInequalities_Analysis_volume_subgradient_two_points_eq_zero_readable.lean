-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradient_two_points_eq_zero_readable
-- name    : FunctionalInequalities.Analysis.volume_subgradient_two_points_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:46.388747+00:00
-- url     : https://prove2.me/theorems/097fae72-0e02-4d52-bbb1-f4883ba49bd8
-- title:
--   Nullity of Two-Point Subgradient Slopes
-- statement:
--   This gives the Alexandrov null-set statement for repeated subgradients.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex. Consider the set of slopes that are subgradients at two distinct points:
--   $$S=\left\{p:\exists x\ne y,\ \forall z,\ u(x)+\langle p,z-x\rangle\le u(z),\ \ u(y)+\langle p,z-y\rangle\le u(z)\right\}.$$
--   Then its volume is zero:
--   $$\operatorname{vol}(S)=0.$$
--
--   This is a measure-theoretic uniqueness statement for subgradients and is used in the push-forward Alexandrov identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem volume_subgradient_two_points_eq_zero [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u) :
--       (volume : Measure E) {p : E | ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
--         (∀ z, u y + ⟪p, z - y⟫ ≤ u z)} = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`ConvexOn.ae_differentiableAt_of_isOpen`](https://prove2.me/theorems/b601dd62-f116-4daf-a684-024dc3b2b841), [`conjugate_maximizer_eq_gradient`](https://prove2.me/theorems/80335e95-bd3b-41ae-b542-89eb54c17879), [`convex_epigraph_legendre`](https://prove2.me/theorems/ae6b66c7-c45b-4b02-ba8a-8dcdbef9e183).
--
--   Previous: [`subgradientImage_subset_of_le`](https://prove2.me/theorems/48dd6fd6-70dd-48c0-b715-081cfd732396) · Next: [`eventually_abs_sub_quadratic_le_of_subgradient_expansion`](https://prove2.me/theorems/4ddfd262-d82d-4fdf-95dc-67ccaaffbd1b).
--
--   [Source excerpt, lines 1113–1116](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L1113-L1116) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L1109-L1217 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.volume_subgradient_two_points_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.volume_subgradient_two_points_eq_zero_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u) :
    (volume : Measure E) {p : E | ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
      (∀ z, u y + ⟪p, z - y⟫ ≤ u z)} = 0 := by sorry
