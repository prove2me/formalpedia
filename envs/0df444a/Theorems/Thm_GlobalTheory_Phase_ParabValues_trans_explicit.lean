-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ParabValues_trans_explicit
-- name    : GlobalTheory.Phase.ParabValues.trans_explicit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:36.885804+00:00
-- url     : https://prove2.me/theorems/7aab4c99-d46d-4160-88e8-77c5aedea3e6
-- title:
--   Parab Values: trans explicit
-- statement:
--   The Parab Values construction uses the trans explicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelParabolicTransformPhase.lean#L32-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelParabolicTransformPhase.lean#L32-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ParabValues
open GlobalTheory.SW.Parab

theorem GlobalTheory.Phase.ParabValues.trans_explicit (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hC : σ.toBlocks₂₁ = 0)
    (φ : Matrix κ ι ℚ → ℂ) (hφ : IsSB φ) :
    IsSB (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) ∧
    TransS σ φ (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) := by sorry
