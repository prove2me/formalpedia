-- Prove2me | Theorems.Thm_GlobalTheory_hasFDerivAt_of_continuous_partials
-- name    : GlobalTheory.hasFDerivAt_of_continuous_partials
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:57.461806+00:00
-- url     : https://prove2.me/theorems/a107980b-09b5-43f0-9c76-894cbc568fad
-- title:
--   Global Theory: has FDeriv At of continuous partials
-- statement:
--   The Global Theory construction uses the has FDeriv At of continuous partials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HasFDerivAtOfContinuousPartials.lean#L46-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HasFDerivAtOfContinuousPartials.lean#L46-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open Filter Topology

theorem GlobalTheory.hasFDerivAt_of_continuous_partials :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by sorry
