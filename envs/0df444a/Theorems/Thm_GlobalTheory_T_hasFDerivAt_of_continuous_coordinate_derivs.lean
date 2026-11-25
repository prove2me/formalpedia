-- Prove2me | Theorems.Thm_GlobalTheory_T_hasFDerivAt_of_continuous_coordinate_derivs
-- name    : GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:49.523751+00:00
-- url     : https://prove2.me/theorems/25531e53-ae43-4499-88da-7ffa912b0ca4
-- title:
--   T: has FDeriv At of continuous coordinate derivs
-- statement:
--   The T construction uses the has FDeriv At of continuous coordinate derivs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HasFDerivAtOfContinuousPartialsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HasFDerivAtOfContinuousPartialsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartialsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ), (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) → (∀ i, Continuous (d i)) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by sorry
