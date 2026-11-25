-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_transport
-- name    : GlobalTheory.DegCnt.PosJ.transport
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:25.513046+00:00
-- url     : https://prove2.me/theorems/2d221537-0504-4b46-9404-9759ade4dbd2
-- title:
--   Pos J: transport
-- statement:
--   The Pos J construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L509-L535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L509-L535

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
open GlobalTheory.HL Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) {j : ℕ}
variable {H} {r : ℕ}

theorem GlobalTheory.DegCnt.PosJ.transport [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (F : FlagD H r) (hj : j ≤ r) (s : V ≃ₗ[K] V) {S u : Matrix (Fin j) (Fin j) K} (hS : IsUni S)
    (hs : ∀ a, s (ej F hj a) = vec (ej F hj) S a) (L : Submodule (𝓞 K) V) (𝔞 : Fin j → Submodule (𝓞 K) K)
    (h1 : ∀ a, ∀ t ∈ 𝔞 a, t • vec (ej F hj) u a ∈ L)
    (h2 : ∀ y ∈ L, y ∈ F.Xa j → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • vec (ej F hj) u a) :
    (∀ a, ∀ t ∈ 𝔞 a, t • vec (ej F hj) (S * u) a ∈ s • L) ∧
    ∀ y ∈ s • L, y ∈ F.Xa j → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧
      y = ∑ a, c a • vec (ej F hj) (S * u) a := by sorry
