-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_inN_of
-- name    : GlobalTheory.DegCnt.PosJ.inN_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:19.745481+00:00
-- url     : https://prove2.me/theorems/c432f38f-a35c-4513-b0e2-ed761e6064c3
-- title:
--   Pos J: in N of
-- statement:
--   The Pos J construction uses the in N of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L609-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L609-L617

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
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.PosJ.inN_of (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (s : V ≃ₗ[K] V) (hiso : ∀ x y, H.B (s x) (s y) = H.B x y)
    {S : Matrix (Fin j) (Fin j) K} (hS : IsUni S) (hs : ∀ a, s (ej F hj a) = vec (ej F hj) S a)
    (hfix : ∀ a : Fin r, j ≤ (a : ℕ) → s (F.e a.castSucc) = F.e a.castSucc)
    (hp : ∀ y, (∀ a, H.B y (ej F hj a) = 0) → s y - y ∈ F.X) : F.InN (s : V →ₗ[K] V) := by sorry
