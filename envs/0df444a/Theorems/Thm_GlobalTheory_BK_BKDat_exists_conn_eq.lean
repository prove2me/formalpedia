-- Prove2me | Theorems.Thm_GlobalTheory_BK_BKDat_exists_conn_eq
-- name    : GlobalTheory.BK.BKDat.exists_conn_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:40.289463+00:00
-- url     : https://prove2.me/theorems/834b8ba5-dac1-4365-9488-1b6d0d8dc4e5
-- title:
--   BKDat: exists conn eq
-- statement:
--   The BKDat construction uses the exists conn eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L128-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L128-L129

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
omit [NeZero e]

theorem GlobalTheory.BK.BKDat.exists_conn_eq {m : Vec K a ι} (hm : m ∈ D.MM) : ∃ w ∈ D.MM, D.conn m = (X : K⟦X⟧) • w := by sorry
