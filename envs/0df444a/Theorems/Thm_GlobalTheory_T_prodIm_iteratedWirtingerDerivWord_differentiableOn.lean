-- Prove2me | Theorems.Thm_GlobalTheory_T_prodIm_iteratedWirtingerDerivWord_differentiableOn
-- name    : GlobalTheory.T.prodIm_iteratedWirtingerDerivWord_differentiableOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:55:15.468462+00:00
-- url     : https://prove2.me/theorems/50607a28-9fea-43bd-a0c7-2fc4e7988cb5
-- title:
--   T: prod Im iterated Wirtinger Deriv Word differentiable On
-- statement:
--   The T construction uses the prod Im iterated Wirtinger Deriv Word differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOnStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOnStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOnStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.prodIm_iteratedWirtingerDerivWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by sorry
