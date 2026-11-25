-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_extc_eq_span
-- name    : GlobalTheory.BK.PhiMod.extc_eq_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:55.082188+00:00
-- url     : https://prove2.me/theorems/c7f8d670-bc4f-4204-b3cc-69d44fb98dfd
-- title:
--   Phi Mod: extc eq span
-- statement:
--   The Phi Mod construction uses the extc eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L177-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L177-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
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
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)

theorem GlobalTheory.BK.PhiMod.extc_eq_span {B : Subalgebra O K⟦X⟧} (h : A O K ≤ B) (τ : ZMod a) :
    P.extc B τ = Submodule.span B (P.Lcomp τ : Set (ι → K⟦X⟧)) := by sorry
