-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_ref_coef
-- name    : GlobalTheory.DegCnt.PosJ.ref_coef
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:48.327554+00:00
-- url     : https://prove2.me/theorems/ef4bb684-6919-44af-8e54-33977e7b1d73
-- title:
--   Pos J: ref coef
-- statement:
--   The Pos J construction uses the ref coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L730-L748
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L730-L748

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
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem GlobalTheory.DegCnt.PosJ.ref_coef (d : V) (A : Submodule (𝓞 K) K)
    (h1 : ∀ b : Fin N.j, ∀ t ∈ N.aa (Fin.castLE N.j_le b), t * H.B (ej N.F N.j_le b) d ∈ A)
    (h2 : ∀ b : Fin N.j, ∀ t ∈ N.aa (Fin.castLE N.j_le b), t * H.B (ej N.F' N.j_le b) d ∈ A)
    (h3 : ∀ b : Fin (r + 1), N.j ≤ (b : ℕ) → H.B (N.F.e b) d = 0)
    (h4 : ∀ b : Fin r, N.j ≤ (b : ℕ) → H.B (N.ist b) d = 0) : ∀ y ∈ N.P0, H.B y d ∈ A := by sorry
