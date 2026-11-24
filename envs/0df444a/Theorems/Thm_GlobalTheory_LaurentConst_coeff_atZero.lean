-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_coeff_atZero
-- name    : GlobalTheory.LaurentConst.coeff_atZero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:39.895632+00:00
-- url     : https://prove2.me/theorems/8065adef-ffe9-42d8-9912-01171e270809
-- title:
--   Laurent Const: coeff at Zero
-- statement:
--   The Laurent Const construction uses the coeff at Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L73-L79

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

theorem GlobalTheory.LaurentConst.coeff_atZero (z : AddMonoidAlgebra R ℤ) (n : ℤ) : (atZero R z).coeff n = z.coeff n := by sorry
