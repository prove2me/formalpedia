-- Prove2me | Theorems.Thm_GlobalTheory_SCV_contDiffOn_nat
-- name    : GlobalTheory.SCV.contDiffOn_nat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:44.005345+00:00
-- url     : https://prove2.me/theorems/fa0e122d-89fb-4b46-b902-401b748eb166
-- title:
--   SCV: cont Diff On nat
-- statement:
--   The SCV construction uses the cont Diff On nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L153-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L153-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem GlobalTheory.SCV.contDiffOn_nat {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ {f : E → V}, DifferentiableOn ℂ f U → ContDiffOn ℂ n f U := by sorry
