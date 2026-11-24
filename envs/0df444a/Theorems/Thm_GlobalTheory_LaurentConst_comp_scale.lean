-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_comp_scale
-- name    : GlobalTheory.LaurentConst.comp_scale
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:34.619938+00:00
-- url     : https://prove2.me/theorems/21acae34-815a-4187-b1dc-158366857606
-- title:
--   Laurent Const: comp scale
-- statement:
--   The Laurent Const construction uses the comp scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L177-L183

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
variable {t}

theorem GlobalTheory.LaurentConst.comp_scale {A : Type} [CommRing A] [IsReduced A] (ht : IsNilpotent ((t : R) - 1))
    (ρ : AddMonoidAlgebra R ℤ →+* A) : ρ.comp (scale r t) = ρ.comp (scale r 1) := by sorry
