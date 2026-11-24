-- Prove2me | Theorems.Thm_GlobalTheory_SW_TransComp_blocks
-- name    : GlobalTheory.SW.TransComp.blocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:55.571815+00:00
-- url     : https://prove2.me/theorems/cc99d67b-e6c3-49ad-8bab-b4eb0ef47080
-- title:
--   Trans Comp: blocks
-- statement:
--   The Trans Comp construction uses the blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationLawMul.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationLawMul.lean#L35-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TransComp
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SW.TransComp.blocks {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ) :
    σ.toBlocks₂₁ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₁ᵀ * σ.toBlocks₂₁ = 0 ∧
      σ.toBlocks₂₂ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₂ᵀ * σ.toBlocks₂₁ = 1 := by sorry
