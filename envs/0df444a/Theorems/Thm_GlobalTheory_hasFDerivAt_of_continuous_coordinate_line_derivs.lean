-- Prove2me | Theorems.Thm_GlobalTheory_hasFDerivAt_of_continuous_coordinate_line_derivs
-- name    : GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:32.192769+00:00
-- url     : https://prove2.me/theorems/6c8b456d-2b70-4d7b-8312-af7b11d0a853
-- title:
--   Global Theory: has FDeriv At of continuous coordinate line derivs
-- statement:
--   The Global Theory construction uses the has FDeriv At of continuous coordinate line derivs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasFDerivAtOfContinuousCoordinatePartials.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasFDerivAtOfContinuousCoordinatePartials.lean#L8-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartials
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasFDerivAtOfContinuousCoordinatePartials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory

theorem GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) →
      (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) →
      ∀ t, HasFDerivAt F
        (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by sorry
