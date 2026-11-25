-- Prove2me | Theorems.Thm_GlobalTheory_T_hasFDerivAt_of_continuous_coordinate_partials
-- name    : GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:54.854634+00:00
-- url     : https://prove2.me/theorems/09c20426-7266-4f41-b97b-8acc59a29316
-- title:
--   T: has FDeriv At of continuous coordinate partials
-- statement:
--   The T construction uses the has FDeriv At of continuous coordinate partials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasFDerivAtOfContinuousCoordinatePartialsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasFDerivAtOfContinuousCoordinatePartialsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasFDerivAtOfContinuousCoordinatePartials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasFDerivAtOfContinuousCoordinatePartialsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) → (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by sorry
