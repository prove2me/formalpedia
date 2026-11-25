-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_exists_frame
-- name    : GlobalTheory.DegCnt.PosJ.exists_frame
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:53:42.236855+00:00
-- url     : https://prove2.me/theorems/5cbfaa47-f8bb-4eae-ba7f-e1ac392df7c7
-- title:
--   Pos J: exists frame
-- statement:
--   The Pos J construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L311-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L311-L396

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
open GlobalTheory.HL
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegCnt.PosJ.exists_frame (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (L : Submodule (𝓞 K) V) {𝔡 : Ideal (𝓞 K)}
    (h : 𝔡 ≠ ⊥) (k : Fin r → ℤ) (hL : ∀ a : Fin r, HermLat.lead F L a.castSucc = ipow 𝔡 (k a)) :
    ∃ u : Matrix (Fin j) (Fin j) K, IsUni u ∧
      (∀ a, ∀ t ∈ ipow 𝔡 (k (Fin.castLE hj a)), t • vec (ej F hj) u a ∈ L) ∧
      ∀ y ∈ L, y ∈ F.Xa j → ∃ c : Fin j → K, (∀ a, c a ∈ ipow 𝔡 (k (Fin.castLE hj a))) ∧
        y = ∑ a, c a • vec (ej F hj) u a := by sorry
