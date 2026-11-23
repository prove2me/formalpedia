-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationPathwiseCongr
-- name    : Kyprianou.Ch01.inverseReciprocalOccupationPathwiseCongr
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T16:04:36.270407+00:00
-- url     : https://prove2.me/theorems/ad7f6376-ad29-4d73-8566-cbde4c94c094
-- title:
--   Pathwise equality implies equality of inverse reciprocal occupation clocks
-- statement:
--   If two integer paths coincide at every physical time along one sample point, their inverse reciprocal-occupation clocks coincide at each branching time, including infinite clock values.
-- source:
--   Kyprianou (2006), Eq. (1.19), deterministic inverse occupation clock extensionality.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseReciprocalOccupationPathwiseCongr
    {Ω : Type*} (W X : ℝ≥0 → Ω → ℤ) (w : Ω)
    (hPath : ∀ s : ℝ≥0, W s w = X s w) (v : ℝ≥0) :
    inverseReciprocalOccupation W v w =
      inverseReciprocalOccupation X v w := by
  sorry
