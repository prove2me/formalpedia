-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CharacterBiduality_indicator_mem_SB
-- name    : GlobalTheory.CompanionTheory.CharacterBiduality.indicator_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:01.310804+00:00
-- url     : https://prove2.me/theorems/961a32a9-88b8-4360-b9bb-ee1fbf77b881
-- title:
--   Character Biduality: indicator mem SB
-- statement:
--   The Character Biduality construction uses the indicator mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCharacterSeparatingLattice.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCharacterSeparatingLattice.lean#L13-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharacterBiduality
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.CharacterBiduality.indicator_mem_SB {n : ℕ} (A : AddSubgroup (Fin n → k))
    (hAc : IsCompact (A : Set (Fin n → k))) (hAo : IsOpen (A : Set (Fin n → k))) :
    (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (Fin n → k) := by sorry
