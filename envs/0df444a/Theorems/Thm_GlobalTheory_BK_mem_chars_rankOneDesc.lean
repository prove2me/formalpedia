-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_chars_rankOneDesc
-- name    : GlobalTheory.BK.mem_chars_rankOneDesc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:48.797352+00:00
-- url     : https://prove2.me/theorems/68e46676-96ee-5f3e-9b9e-58bc27f281a5
-- title:
--   BK: mem chars rank One Desc
-- statement:
--   The BK construction uses the mem chars rank One Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L462-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L462-L466

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
omit [NeZero a] [TameDescentExponentData K l e a]
variable [TameDescentExponentData K l e 1]

theorem GlobalTheory.BK.mem_chars_rankOneDesc (j : ℤ) (c : ZMod e) :
    c ∈ (rankOneDesc (K := K) (l := l) j (omegaOne O ^ c.val)).chars 0 := by sorry
