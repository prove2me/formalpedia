-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_near_of
-- name    : GlobalTheory.DegCnt.PosJ.near_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:37.654047+00:00
-- url     : https://prove2.me/theorems/e145d417-6c2f-4f0f-9c26-efdee7625b56
-- title:
--   Pos J: near of
-- statement:
--   The Pos J construction uses the near of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L229-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L229-L278

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
omit [NumberField K] [StarRing K]

theorem GlobalTheory.DegCnt.PosJ.near_of {j m : ℕ} (e : Fin j → V) (X : Submodule K V) (L P : Submodule (𝓞 K) V)
    (𝔞 : Fin j → Submodule (𝓞 K) K) (u : Matrix (Fin j) (Fin j) K) (hu : IsUni u) (𝔮 : Ideal (𝓞 K))
    (hq : ∀ x ∈ 𝔮, ∀ a b, ∀ t ∈ 𝔞 a, (x : K) * (t * u b a) ∈ 𝔞 b)
    (h1 : ∀ a, ∀ t ∈ 𝔞 a, t • vec e u a ∈ L)
    (h2 : ∀ y ∈ L, y ∈ X → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • vec e u a)
    (hP1 : ∀ a, ∀ t ∈ 𝔞 a, t • e a ∈ P)
    (hP2 : ∀ y ∈ P, y ∈ X → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • e a)
    (hm : j ≤ m) (hm1 : 1 ≤ m) :
    𝔮 ^ m • (P ⊓ rs (𝓞 K) X) ≤ L ∧ 𝔮 ^ m • (L ⊓ rs (𝓞 K) X) ≤ P := by sorry
