-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_hatSpan_extc
-- name    : GlobalTheory.BK.PhiMod.hatSpan_extc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:37.391555+00:00
-- url     : https://prove2.me/theorems/eafa3c72-4ac6-4e89-ba06-65e0b2510046
-- title:
--   Phi Mod: hat Span extc
-- statement:
--   The Phi Mod construction uses the hat Span extc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L552-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L552-L569

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
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable {O K}
variable {ι}
open GlobalTheory.BK.PhiMod
variable {l e a} (P : PhiMod O K l e a ι)

theorem GlobalTheory.BK.PhiMod.hatSpan_extc {B : Subalgebra O K⟦X⟧} (hB : B ≤ Rpi O K l e) (τ : ZMod a) :
    hatSpan O l e (P.extc B τ) =
      Submodule.span _ (Set.range fun j => hatV O l e ((P.mx τ).col j)) := by sorry
