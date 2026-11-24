-- Prove2me | Theorems.Thm_GlobalTheory_SiegelAction_toBlocks_mul
-- name    : GlobalTheory.SiegelAction.toBlocks_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:11:31.992936+00:00
-- url     : https://prove2.me/theorems/22ae393d-b9cd-4c5d-9ff2-ea0a94719d4b
-- title:
--   Siegel Action: to Blocks mul
-- statement:
--   The Siegel Action construction uses the to Blocks mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L168-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L168-L174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem GlobalTheory.SiegelAction.toBlocks_mul (σ' σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₁₁ = σ'.toBlocks₁₁ * σ.toBlocks₁₁ + σ'.toBlocks₁₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₁₂ = σ'.toBlocks₁₁ * σ.toBlocks₁₂ + σ'.toBlocks₁₂ * σ.toBlocks₂₂ ∧
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₂₂ = σ'.toBlocks₂₁ * σ.toBlocks₁₂ + σ'.toBlocks₂₂ * σ.toBlocks₂₂ := by sorry
