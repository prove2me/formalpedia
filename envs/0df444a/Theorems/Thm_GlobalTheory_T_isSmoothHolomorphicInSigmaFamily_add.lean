-- Prove2me | Theorems.Thm_GlobalTheory_T_isSmoothHolomorphicInSigmaFamily_add
-- name    : GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:01.153867+00:00
-- url     : https://prove2.me/theorems/4a9e35a6-9311-44fe-940e-5d52b1c7e46b
-- title:
--   T: is Smooth Holomorphic In Sigma Family add
-- statement:
--   The T construction uses the is Smooth Holomorphic In Sigma Family add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAddStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAddStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAddStatement
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

theorem GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by sorry
