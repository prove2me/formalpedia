-- Prove2me | Theorems.Thm_GlobalTheory_Phase_transS_unique
-- name    : GlobalTheory.Phase.transS_unique
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:28:19.862913+00:00
-- url     : https://prove2.me/theorems/91a9a7e5-f343-4e8e-92d0-beae8651cf91
-- title:
--   Phase: trans S unique
-- statement:
--   The Phase construction uses the trans S unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TransSUnique.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TransSUnique.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSUnique
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
open GlobalTheory GlobalTheory.Phase

theorem GlobalTheory.Phase.transS_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by sorry
