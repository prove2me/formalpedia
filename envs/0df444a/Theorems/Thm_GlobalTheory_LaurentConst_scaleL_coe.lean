-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_scaleL_coe
-- name    : GlobalTheory.LaurentConst.scaleL_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:12.730654+00:00
-- url     : https://prove2.me/theorems/c87952f3-87bf-4a60-8d3d-386e4d1a8c9b
-- title:
--   Laurent Const: scale L coe
-- statement:
--   The Laurent Const construction uses the scale L coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L125-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open AddMonoidAlgebra
attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
variable {L R : Type} [CommRing L] [CommRing R]
variable (r : L →+* R) (t : Rˣ)

theorem GlobalTheory.LaurentConst.scaleL_coe (p : PowerSeries L) : scaleL r t (HahnSeries.ofPowerSeries ℤ L p) =
    HahnSeries.ofPowerSeries ℤ R (scaleP r t p) := by sorry
