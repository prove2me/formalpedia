-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_iff
-- name    : GlobalTheory.DegCnt.Absorb.mem_ipow_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:17:15.936029+00:00
-- url     : https://prove2.me/theorems/146b9101-9c6f-5f32-8093-18de57cd3d31
-- title:
--   Absorb: mem ipow iff
-- statement:
--   The Absorb construction uses the mem ipow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsStarStableIdealAbsorbingMinors.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsStarStableIdealAbsorbingMinors.lean#L31-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
variable {K : Type} [Field K] [NumberField K]
open NumberField
open scoped Pointwise ENNReal Classical nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.DegCnt.Absorb.mem_ipow_iff {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) (x : K) :
    x ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 n ↔ ∀ u ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 (-n),
      x * u ∈ (1 : Submodule (𝓞 K) K) := by sorry
