-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_exists_isom
-- name    : GlobalTheory.DegCnt.PosJ.exists_isom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:14.242892+00:00
-- url     : https://prove2.me/theorems/a9e29f61-e0b2-4f1a-8845-5d39f1e030e5
-- title:
--   Pos J: exists isom
-- statement:
--   The Pos J construction uses the exists isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L413-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L413-L471

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

theorem GlobalTheory.DegCnt.PosJ.exists_isom [FiniteDimensional K V] (e d : Fin j → V) (M M' : Matrix (Fin j) (Fin j) K)
    (hee : ∀ a b, H.B (e a) (e b) = 0) (hdd : ∀ a b, H.B (d a) (d b) = 0)
    (hed : ∀ a b, H.B (e a) (d b) = if a = b then 1 else 0) (hM : Mᵀ * M'.map star = 1) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧
      ∀ y, s y = y + ∑ a, H.B y (d a) • (vec e M a - e a) + ∑ a, H.B y (e a) • (vec d M' a - d a) := by sorry
