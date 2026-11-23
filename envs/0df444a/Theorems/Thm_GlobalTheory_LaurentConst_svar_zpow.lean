-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_svar_zpow
-- name    : GlobalTheory.LaurentConst.svar_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:07.933679+00:00
-- url     : https://prove2.me/theorems/d84bb74e-7f28-4876-8587-35e87ad8bb5a
-- title:
--   Laurent Const: svar zpow
-- statement:
--   The Laurent Const construction uses the svar zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L45-L51

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

theorem GlobalTheory.LaurentConst.svar_zpow (n : ℤ) : ((svar R ^ n : (LaurentSeries R)ˣ) : LaurentSeries R) =
    HahnSeries.single n 1 := by sorry
