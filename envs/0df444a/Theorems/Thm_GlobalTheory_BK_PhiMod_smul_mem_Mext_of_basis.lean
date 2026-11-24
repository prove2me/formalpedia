-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_smul_mem_Mext_of_basis
-- name    : GlobalTheory.BK.PhiMod.smul_mem_Mext_of_basis
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:17:09.928457+00:00
-- url     : https://prove2.me/theorems/143c3ca5-51d0-4542-9fec-9aa25c90e457
-- title:
--   Phi Mod: smul mem Mext of basis
-- statement:
--   The Phi Mod construction uses the smul mem Mext of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L282-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L282-L287

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

theorem GlobalTheory.BK.PhiMod.smul_mem_Mext_of_basis {c : K⟦X⟧} (h : ∀ i, c • P.phi (bas i) ∈ P.M) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.ext B) : c • m ∈ P.Mext B := by sorry
