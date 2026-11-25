-- Prove2me | Theorems.Thm_GlobalTheory_BK_BKDat_plusMod_lower
-- name    : GlobalTheory.BK.BKDat.plusMod_lower
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:52.925925+00:00
-- url     : https://prove2.me/theorems/aec16309-5f2d-5b08-9bdd-163d90260bff
-- title:
--   BKDat: plus Mod lower
-- statement:
--   The BKDat construction uses the plus Mod lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L215-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L215-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
open GlobalTheory.BK.BKDat
variable (D : BKDat O K l e a ι η H)
variable {D} {y : Vec K a ι}
omit [NeZero e]

theorem GlobalTheory.BK.BKDat.plusMod_lower (hy : y ∈ D.Y) :
    ∀ v ∈ (plusMod hy).M, E K l e ^ (H + η) • v ∈ (plusMod hy).L := by sorry
