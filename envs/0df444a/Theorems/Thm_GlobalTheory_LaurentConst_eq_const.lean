-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_eq_const
-- name    : GlobalTheory.LaurentConst.eq_const
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:29.98458+00:00
-- url     : https://prove2.me/theorems/d5b2a647-11bb-4549-88e7-3f2626d3c91c
-- title:
--   Laurent Const: eq const
-- statement:
--   The Laurent Const construction uses the eq const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L89-L100

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

theorem GlobalTheory.LaurentConst.eq_const {z : AddMonoidAlgebra R ℤ} {p q : PowerSeries R}
    (hp : atZero R z = HahnSeries.ofPowerSeries ℤ R p)
    (hq : atInf R z = HahnSeries.ofPowerSeries ℤ R q) :
    z = algebraMap R _ (PowerSeries.constantCoeff p) := by sorry
