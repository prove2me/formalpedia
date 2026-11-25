-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_mem_ipow_of
-- name    : GlobalTheory.DegCnt.PosJ.mem_ipow_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:07.968503+00:00
-- url     : https://prove2.me/theorems/68578293-0d8a-480e-9090-46692d76bcb3
-- title:
--   Pos J: mem ipow of
-- statement:
--   The Pos J construction uses the mem ipow of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L172-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L172-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.DegCnt.PosJ.mem_ipow_of {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (hx : ∀ y ∈ ipow 𝔡 m, y * x ∈ ipow 𝔡 (m + n)) : x ∈ ipow 𝔡 n := by sorry
