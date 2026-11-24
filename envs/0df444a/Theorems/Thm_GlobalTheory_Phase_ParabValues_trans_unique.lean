-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ParabValues_trans_unique
-- name    : GlobalTheory.Phase.ParabValues.trans_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:33.602351+00:00
-- url     : https://prove2.me/theorems/21fcb7c0-aa28-4ec5-aaa5-0d377ba98c46
-- title:
--   Parab Values: trans unique
-- statement:
--   The Parab Values construction uses the trans unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelParabolicTransformPhase.lean#L103-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelParabolicTransformPhase.lean#L103-L114

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

theorem GlobalTheory.Phase.ParabValues.trans_unique (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    (φ ψ ψ' : Matrix κ ι ℚ → ℂ) (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by sorry
