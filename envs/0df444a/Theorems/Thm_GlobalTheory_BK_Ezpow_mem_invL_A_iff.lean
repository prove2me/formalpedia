-- Prove2me | Theorems.Thm_GlobalTheory_BK_Ezpow_mem_invL_A_iff
-- name    : GlobalTheory.BK.Ezpow_mem_invL_A_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:06:06.57021+00:00
-- url     : https://prove2.me/theorems/bec7fc0d-15ca-51f8-bfd6-b1518b69a88b
-- title:
--   BK: Ezpow mem inv L A iff
-- statement:
--   The BK construction uses the Ezpow mem inv L A iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L297-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L297-L305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Rot_invL

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

theorem GlobalTheory.BK.Ezpow_mem_invL_A_iff {i : ℤ} : Ezpow K l e i ∈ invL l (A O K) ↔ 0 ≤ i := by sorry
