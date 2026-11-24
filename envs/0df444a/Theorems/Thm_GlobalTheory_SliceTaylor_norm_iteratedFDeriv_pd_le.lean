-- Prove2me | Theorems.Thm_GlobalTheory_SliceTaylor_norm_iteratedFDeriv_pd_le
-- name    : GlobalTheory.SliceTaylor.norm_iteratedFDeriv_pd_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:05.212659+00:00
-- url     : https://prove2.me/theorems/82a0f287-6637-4d64-b526-08333c991362
-- title:
--   Slice Taylor: norm iterated FDeriv pd le
-- statement:
--   The Slice Taylor construction uses the norm iterated FDeriv pd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivPdLe.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivPdLe.lean#L38-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceTaylor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceTaylor.norm_iteratedFDeriv_pd_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : X) (g : SchwartzMap X ℂ) (n : ℕ) (w : X) :
    ‖iteratedFDeriv ℝ n (pd a g) w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g w‖ := by sorry
