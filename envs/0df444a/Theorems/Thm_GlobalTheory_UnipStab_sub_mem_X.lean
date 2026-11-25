-- Prove2me | Theorems.Thm_GlobalTheory_UnipStab_sub_mem_X
-- name    : GlobalTheory.UnipStab.sub_mem_X
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:48.867584+00:00
-- url     : https://prove2.me/theorems/8b7bd34d-2dfb-5285-b3a7-0c1d7556b7a6
-- title:
--   Unip Stab: sub mem X
-- statement:
--   The Unip Stab construction uses the sub mem X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairCommonUnipotentStabiliserSummary.lean#L312-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairCommonUnipotentStabiliserSummary.lean#L312-L315

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

theorem GlobalTheory.UnipStab.sub_mem_X {g : V →ₗ[K] V} (hg : F.InN g) {S : Submodule K V} (hS : F.X ≤ S) {y : V}
    (hy : y ∈ perp H S) : g y - y ∈ F.X := by sorry
