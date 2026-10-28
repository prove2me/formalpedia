-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable
-- name    : FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:00.075913+00:00
-- url     : https://prove2.me/theorems/80255608-689e-4cd7-80cc-3b2a722fd329
-- title:
--   Tilted Integration By Parts For Lipschitz Functions
-- statement:
--   This statement establishes weighted integration by parts for a bounded Lipschitz test.
--
--   Let n be a natural number, let U and η be functions on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let L and Lη be nonnegative-real Lipschitz constants. Assume U is L-Lipschitz, η is Lη-Lipschitz, η is bounded by C in norm, and
--
--   $$\int_E e^{-U(x)}\,dx=1.$$
--
--   For every v∈E, both directional derivatives are integrable with respect to $d\nu=e^{-U}dx$, namely $D_vη$ and $ηD_vU$, and
--
--   $$\int_E D_vη\,d\nu=\int_E η\,D_vU\,d\nu.$$
--
--   This is a reusable first-order integration-by-parts identity for normalized exponential tilts in finite dimensions.
--
--   **Formalization Note** The functions are only assumed globally Lipschitz; the derivatives are Fréchet derivatives where represented by `fderiv`, and the tilted measure uses the potential −U.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz {n : ℕ}
--       {U eta : EuclideanSpace ℝ (Fin n) → ℝ} {L Leta : NNReal}
--       (hU : LipschitzWith L U) (heta : LipschitzWith Leta eta)
--       (C : ℝ) (hbound : ∀ x, ‖eta x‖ ≤ C)
--       (hnorm : (∫ x, Real.exp (-U x) ∂volume) = 1)
--       (v : EuclideanSpace ℝ (Fin n)) :
--       Integrable (fun x => fderiv ℝ eta x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
--       Integrable (fun x => eta x * fderiv ℝ U x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
--       (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
--         ∫ x, eta x * fderiv ℝ U x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/LipschitzHessian`](https://prove2.me/theorems/a33bc411-81aa-4352-b34a-c6253ee0ed0a).
--
--   Supporting theorems: [`HasWeakDerivAlong.mul_of_locally_bounded`](https://prove2.me/theorems/1133273b-c737-4c38-bf2a-2953cd23a941), [`hasWeakDerivAlong_exp_neg_of_lipschitz`](https://prove2.me/theorems/bacd1f1f-068d-4e42-88a3-d15ac6d6ee33), [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9), [`integral_eq_zero_of_integrable_weak_derivative`](https://prove2.me/theorems/4bbf5126-d256-459b-9474-606b9a141762).
--
--   Previous: [`integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul`](https://prove2.me/theorems/6627935a-8ab5-4069-9ba3-e8134c1348f4).
--
--   [Source excerpt, lines 238–247](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean#L238-L247) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean#L235-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, declaration `FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian

open MeasureTheory Filter Set
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable {n : ℕ}
    {U eta : EuclideanSpace ℝ (Fin n) → ℝ} {L Leta : NNReal}
    (hU : LipschitzWith L U) (heta : LipschitzWith Leta eta)
    (C : ℝ) (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hnorm : (∫ x, Real.exp (-U x) ∂volume) = 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => fderiv ℝ eta x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    Integrable (fun x => eta x * fderiv ℝ U x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
      ∫ x, eta x * fderiv ℝ U x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) := by sorry
