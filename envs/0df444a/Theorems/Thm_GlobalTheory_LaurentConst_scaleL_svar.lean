-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_scaleL_svar
-- name    : GlobalTheory.LaurentConst.scaleL_svar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:24.276274+00:00
-- url     : https://prove2.me/theorems/cf8209da-d608-4dbe-9ff2-a0368b7e0a24
-- title:
--   Laurent Const: scale L svar
-- statement:
--   The Laurent Const construction uses the scale L svar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L132-L134

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

theorem GlobalTheory.LaurentConst.scaleL_svar : scaleL r t (svar L : LaurentSeries L) =
    HahnSeries.C (t : R) * (svar R : LaurentSeries R) := by sorry
