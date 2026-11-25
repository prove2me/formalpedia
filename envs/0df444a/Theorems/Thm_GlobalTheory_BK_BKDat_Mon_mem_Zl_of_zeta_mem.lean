-- Prove2me | Theorems.Thm_GlobalTheory_BK_BKDat_Mon_mem_Zl_of_zeta_mem
-- name    : GlobalTheory.BK.BKDat.Mon_mem_Zl_of_zeta_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:37.274019+00:00
-- url     : https://prove2.me/theorems/cd8f86ec-3562-4216-900a-0ab2e34e88a8
-- title:
--   BKDat: Mon mem Zl of zeta mem
-- statement:
--   The BKDat construction uses the Mon mem Zl of zeta mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L186-L191

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

theorem GlobalTheory.BK.BKDat.Mon_mem_Zl_of_zeta_mem {y : Vec K a ι} (hy : y ∈ D.Yl)
    (hz : D.zeta y ∈ D.ext (Rpi O K l e)) : D.Mon y ∈ D.Zl := by sorry
