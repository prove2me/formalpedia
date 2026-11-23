-- Prove2me | Theorems.Thm_GlobalTheory_SCV_eqOn_of_eventuallyEq
-- name    : GlobalTheory.SCV.eqOn_of_eventuallyEq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:46.628736+00:00
-- url     : https://prove2.me/theorems/96931f05-c9a2-4a07-80eb-f39f0d06c414
-- title:
--   SCV: eq On of eventually Eq
-- statement:
--   The SCV construction uses the eq On of eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L325-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L325-L329

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

theorem GlobalTheory.SCV.eqOn_of_eventuallyEq {f g : E → V} {U : Set E} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {c : E} (hc : c ∈ U)
    (hfg : f =ᶠ[𝓝 c] g) : EqOn f g U := by sorry
