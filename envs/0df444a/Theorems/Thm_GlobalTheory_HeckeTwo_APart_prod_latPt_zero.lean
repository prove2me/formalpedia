-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_APart_prod_latPt_zero
-- name    : GlobalTheory.HeckeTwo.APart.prod_latPt_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:46.311472+00:00
-- url     : https://prove2.me/theorems/10b69269-faa8-44b2-81a1-55b4dc2e9cec
-- title:
--   APart: prod lat Pt zero
-- statement:
--   The APart construction uses the prod lat Pt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinConstantTermPartDifferentiableOn.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinConstantTermPartDifferentiableOn.lean#L65-L69

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
variable [IsTotallyReal F]

theorem GlobalTheory.HeckeTwo.APart.prod_latPt_zero (a : F) :
    ∏ τ : Emb F, latPt 0 (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F) * ((Algebra.norm ℚ a : ℚ) : ℂ) := by sorry
