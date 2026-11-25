-- Prove2me | Theorems.Thm_GlobalTheory_BK_Descent_tameDescent_extended_action_extraVector
-- name    : GlobalTheory.BK.Descent.tameDescent_extended_action_extraVector
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:55.476175+00:00
-- url     : https://prove2.me/theorems/7dba953f-cd1c-5a20-8a6e-a3ed4cc80729
-- title:
--   Descent: tame Descent extended action extra Vector
-- statement:
--   The Descent construction uses the tame Descent extended action extra Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L234-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L234-L235

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
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
variable (Δ : Descent P) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv)

theorem GlobalTheory.BK.Descent.tameDescent_extended_action_extraVector (g : TameGal K l e a) : (Δ.plus hy hinv).act g xVec = xVec := by sorry
