-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_phi_mem_ext
-- name    : GlobalTheory.BK.PhiMod.phi_mem_ext
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:38.181195+00:00
-- url     : https://prove2.me/theorems/31b63d81-554f-44c3-a7fc-d24f39df143d
-- title:
--   Phi Mod: phi mem ext
-- statement:
--   The Phi Mod construction uses the phi mem ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L284-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L284-L286

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
variable [Fact l.Prime]

theorem GlobalTheory.BK.PhiMod.phi_mem_ext {B : Subalgebra O K⟦X⟧} (hB : ∀ f ∈ B, frob K l f ∈ B) {v : Vec K a ι}
    (hv : v ∈ P.Mext B) : P.phi v ∈ P.ext B := by sorry
