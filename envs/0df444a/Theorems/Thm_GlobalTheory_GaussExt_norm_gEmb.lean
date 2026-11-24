-- Prove2me | Theorems.Thm_GlobalTheory_GaussExt_norm_gEmb
-- name    : GlobalTheory.GaussExt.norm_gEmb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:56.325839+00:00
-- url     : https://prove2.me/theorems/5a06aac3-fdd0-4e4d-a523-9e6beb6c18c7
-- title:
--   Gauss Ext: norm g Emb
-- statement:
--   The Gauss Ext construction uses the norm g Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlgebraNormRatGaussianExtensionOfPair.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlgebraNormRatGaussianExtensionOfPair.lean#L46-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.GaussExt
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.GaussExt.norm_gEmb (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by sorry
