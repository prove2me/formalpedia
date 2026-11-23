-- Prove2me | Theorems.Thm_GlobalTheory_SW_HAct_mul_blocks
-- name    : GlobalTheory.SW.HAct.mul_blocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:39.881323+00:00
-- url     : https://prove2.me/theorems/a2d223cd-acb0-4ded-97f7-a64dad1e6ec8
-- title:
--   HAct: mul blocks
-- statement:
--   The HAct construction uses the mul blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L204-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L204-L215

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem GlobalTheory.SW.HAct.mul_blocks (τ : E →+* ℂ) (γ γ' : M2 E N) :
    (γ' * γ).toBlocks₁₁.map τ = γ'.toBlocks₁₁.map τ * γ.toBlocks₁₁.map τ +
        γ'.toBlocks₁₂.map τ * γ.toBlocks₂₁.map τ ∧
    (γ' * γ).toBlocks₁₂.map τ = γ'.toBlocks₁₁.map τ * γ.toBlocks₁₂.map τ +
        γ'.toBlocks₁₂.map τ * γ.toBlocks₂₂.map τ ∧
    (γ' * γ).toBlocks₂₁.map τ = γ'.toBlocks₂₁.map τ * γ.toBlocks₁₁.map τ +
        γ'.toBlocks₂₂.map τ * γ.toBlocks₂₁.map τ ∧
    (γ' * γ).toBlocks₂₂.map τ = γ'.toBlocks₂₁.map τ * γ.toBlocks₁₂.map τ +
        γ'.toBlocks₂₂.map τ * γ.toBlocks₂₂.map τ := by sorry
