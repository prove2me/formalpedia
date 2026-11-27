-- Prove2me | Theorems.Thm_GlobalTheory_WeberProduct_oddProd_neg_mul
-- name    : GlobalTheory.WeberProduct.oddProd_neg_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:35:31.731264+00:00
-- url     : https://prove2.me/theorems/2a4cf58d-324d-56b1-801d-13cfb6ec83c9
-- title:
--   Weber Product: odd Prod neg mul
-- statement:
--   The Weber Product construction uses the odd Prod neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionProductEqSqrtTwo.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeberFunctionProductEqSqrtTwo.lean#L42-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionProductEqSqrtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.WeberProduct

theorem GlobalTheory.WeberProduct.oddProd_neg_mul {t : ℂ} (ht : ‖t‖ < 1) : oddProd (-t) * oddProd t = oddProd (t ^ 2) := by sorry
