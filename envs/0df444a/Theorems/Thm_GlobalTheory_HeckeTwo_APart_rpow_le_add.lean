-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_APart_rpow_le_add
-- name    : GlobalTheory.HeckeTwo.APart.rpow_le_add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:47.373796+00:00
-- url     : https://prove2.me/theorems/41d8f686-e6e3-494d-92eb-917e0d6f5fe8
-- title:
--   APart: rpow le add
-- statement:
--   The APart construction uses the rpow le add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinConstantTermPartDifferentiableOn.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinConstantTermPartDifferentiableOn.lean#L55-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.APart
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwo.APart.rpow_le_add {x : ℝ} (hx : 0 < x) {r t R : ℝ} (hr : r ≤ t) (hR : t ≤ R) :
    x ^ (-2 * t) ≤ x ^ (-2 * r) + x ^ (-2 * R) := by sorry
