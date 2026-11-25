-- Prove2me | Theorems.Thm_GlobalTheory_BK_filL_rankOne
-- name    : GlobalTheory.BK.filL_rankOne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:10:29.506821+00:00
-- url     : https://prove2.me/theorems/c1ec4dd5-625e-4313-ad7f-307b9e93a8a3
-- title:
--   BK: fil L rank One
-- statement:
--   The BK construction uses the fil L rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L314-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L314-L330

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

theorem GlobalTheory.BK.filL_rankOne (j i : ℤ) : (rankOne O K l e fun _ : ZMod a => j).filL i =
    shiftE l e (if i ≤ j then j else j + 1)
      ((rankOne O K l e fun _ : ZMod a => j).Mext (invL l (A O K))) := by sorry
