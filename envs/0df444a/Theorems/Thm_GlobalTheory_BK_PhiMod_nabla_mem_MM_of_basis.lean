-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_nabla_mem_MM_of_basis
-- name    : GlobalTheory.BK.PhiMod.nabla_mem_MM_of_basis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:17:30.480504+00:00
-- url     : https://prove2.me/theorems/056469ea-76b7-45bc-bc02-1333dabcb30a
-- title:
--   Phi Mod: nabla mem MM of basis
-- statement:
--   The Phi Mod construction uses the nabla mem MM of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L254-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L254-L261

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
omit [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem GlobalTheory.BK.PhiMod.nabla_mem_MM_of_basis (h : ∀ i, P.nabla (P.phi (bas i)) ∈ P.MM)
    (h' : ∀ i, P.phi (bas i) ∈ P.MM) {m : Vec K a ι} (hm : m ∈ P.MM) : P.nabla m ∈ P.MM := by sorry
