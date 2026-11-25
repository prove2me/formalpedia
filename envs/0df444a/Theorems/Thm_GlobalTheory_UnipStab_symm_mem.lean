-- Prove2me | Theorems.Thm_GlobalTheory_UnipStab_symm_mem
-- name    : GlobalTheory.UnipStab.symm_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:58.242162+00:00
-- url     : https://prove2.me/theorems/33422d42-f4bb-4aa6-9056-d58ad87ac494
-- title:
--   Unip Stab: symm mem
-- statement:
--   The Unip Stab construction uses the symm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairCommonUnipotentStabiliserSummary.lean#L163-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairCommonUnipotentStabiliserSummary.lean#L163-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnipStab
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
variable {F}

theorem GlobalTheory.UnipStab.symm_mem [FiniteDimensional K V] (s : V ≃ₗ[K] V) (S : Submodule K V)
    (h : ∀ x ∈ S, s x ∈ S) {x : V} (hx : x ∈ S) : s.symm x ∈ S := by sorry
