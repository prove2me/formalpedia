-- Prove2me | Theorems.Thm_GlobalTheory_T_algebraNorm_rat_gaussianExtensionOfPair
-- name    : GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:39.549912+00:00
-- url     : https://prove2.me/theorems/c32e898d-2263-4438-9e7e-59a27b557343
-- title:
--   T: algebra Norm rat gaussian Extension Of Pair
-- statement:
--   The T construction uses the algebra Norm rat gaussian Extension Of Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlgebraNormRatGaussianExtensionOfPairStatement.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlgebraNormRatGaussianExtensionOfPairStatement.lean#L15-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPair
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPairStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (a b : F), ((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by sorry
