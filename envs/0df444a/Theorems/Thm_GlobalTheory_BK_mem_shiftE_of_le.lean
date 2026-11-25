-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_shiftE_of_le
-- name    : GlobalTheory.BK.mem_shiftE_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:40:16.896266+00:00
-- url     : https://prove2.me/theorems/04a6a231-9f30-49c4-8f4b-6905e742e557
-- title:
--   BK: mem shift E of le
-- statement:
--   The BK construction uses the mem shift E of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L307-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L307-L312

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

theorem GlobalTheory.BK.mem_shiftE_of_le {P : PhiMod O K l e a ι} {i k : ℤ} (h : i ≤ k) {v : Vec K a ι}
    (hv : v ∈ shiftE l e k (P.Mext (invL l (A O K)))) :
    v ∈ shiftE l e i (P.Mext (invL l (A O K))) := by sorry
