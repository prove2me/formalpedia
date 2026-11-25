-- Prove2me | Theorems.Thm_GlobalTheory_BK_BKHom_onPol_Lc
-- name    : GlobalTheory.BK.BKHom.onPol_Lc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:19.651035+00:00
-- url     : https://prove2.me/theorems/66f268b6-20f3-4793-bb86-a2d6920926f1
-- title:
--   BKHom: on Pol Lc
-- statement:
--   The BKHom construction uses the on Pol Lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L193-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L193-L196

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

theorem GlobalTheory.BK.BKHom.onPol_Lc {D : BKDat O K l e a ι η H} {D' : BKDat O K l e a κ η' H'}
    (F : BKHom D D') (w : D.Pol) : F.onPol (D.Lc w) = D'.Lc (F.onPol w) := by sorry
