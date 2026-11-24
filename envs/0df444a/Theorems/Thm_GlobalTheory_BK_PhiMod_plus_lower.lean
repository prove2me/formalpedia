-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_plus_lower
-- name    : GlobalTheory.BK.PhiMod.plus_lower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:17:26.05386+00:00
-- url     : https://prove2.me/theorems/24a3db94-06ce-46bb-8f22-8575dadb26f6
-- title:
--   Phi Mod: plus lower
-- statement:
--   The Phi Mod construction uses the plus lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L311-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L311-L320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.PhiMod
omit [NeZero a] [TameDescentExponentData K l e a]
variable (P : PhiMod O K l e a ι)
variable {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
omit [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem GlobalTheory.BK.PhiMod.plus_lower {n : ℕ} (h : ∀ v ∈ P.M, E K l e ^ n • v ∈ P.L) (hn : E K l e ^ n • y ∈ P.L) :
    ∀ v ∈ (P.plus hy).M, E K l e ^ n • v ∈ (P.plus hy).L := by sorry
