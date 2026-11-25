-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_nat
-- name    : GlobalTheory.DegCnt.Absorb.mem_ipow_nat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:08:46.870781+00:00
-- url     : https://prove2.me/theorems/d7f77cc2-de8c-4d7c-8ed0-d07185ba675b
-- title:
--   Absorb: mem ipow nat
-- statement:
--   The Absorb construction uses the mem ipow nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsStarStableIdealAbsorbingMinors.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsStarStableIdealAbsorbingMinors.lean#L22-L25

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

theorem GlobalTheory.DegCnt.Absorb.mem_ipow_nat (𝔡 : Ideal (𝓞 K)) (n : ℕ) (x : K) :
    x ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 n ↔ ∃ d ∈ 𝔡 ^ n, (d : K) = x := by sorry
