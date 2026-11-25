-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_exists_elt
-- name    : GlobalTheory.DegCnt.PosJ.exists_elt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:48.820216+00:00
-- url     : https://prove2.me/theorems/acf5b2cc-a1cc-50ec-a2be-381a348f7f2b
-- title:
--   Pos J: exists elt
-- statement:
--   The Pos J construction uses the exists elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L620-L721
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L620-L721

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
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
variable (N : NF H r)
set_option maxHeartbeats 800000

theorem GlobalTheory.DegCnt.PosJ.exists_elt [FiniteDimensional K V] (u : Matrix (Fin N.j) (Fin N.j) K) (hu : IsUni u) :
    ∃ s ∈ N.Rs, (∀ y ∈ II N.F N.F' ⊔ Submodule.span K {N.F.z} ⊔ N.Ist, s y = y) ∧
      (∀ x y, H.B (s x) (s y) = H.B x y) ∧
      ∃ M S : Matrix (Fin N.j) (Fin N.j) K, IsUni M ∧ IsUni S ∧
        (∀ a, s (ej N.F N.j_le a) = vec (ej N.F N.j_le) M a) ∧
        (∀ a, s (ej N.F' N.j_le a) = vec (ej N.F' N.j_le) S a) ∧
        ∀ a b : Fin N.j, sameBlock N.w.blocks a b = true → a ≠ b → (M * u) a b = 0 := by sorry
