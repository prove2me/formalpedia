-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_center_multiplier_bound
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center_multiplier_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:34:55.970266+00:00
-- url     : https://prove2.me/theorems/b1192a8f-1415-47a3-9e09-5535e4d733e9
-- title:
--   Local center bound for bounded multipliers
-- statement:
--   For any index and any natural multiplier bounded by K, prove the local exponential center estimate. The proof uses the approximation assumption at i.val, identifies the rational center minus period with twice the imaginary unit times the real approximation error, and uses the ceiling defining the fixed weight to bound the denominator contribution. The arbitrary multiplier makes the lemma reusable and lets the parent discharge its row-dependent case using r.1.val < K.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center_multiplier_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) (i : Fin d.m)
    (k : ℕ) (hk : k ≤ d.K) :
    ‖(k : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period)‖ ≤
      Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i) := by sorry
