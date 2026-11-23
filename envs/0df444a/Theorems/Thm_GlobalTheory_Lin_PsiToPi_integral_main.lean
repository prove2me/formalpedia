-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_integral_main
-- name    : GlobalTheory.Lin.PsiToPi.integral_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:19.257651+00:00
-- url     : https://prove2.me/theorems/7b4e39ff-0ba4-4328-af53-5d1e11336918
-- title:
--   Psi To Pi: integral main
-- statement:
--   The Psi To Pi construction uses the integral main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L73-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)

theorem GlobalTheory.Lin.PsiToPi.integral_main (θ : ℤ) {β Y X : ℝ} (hβ : 0 < β) (hY : 1 < Y) (hYX : Y ≤ X) :
    ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * mainPsi θ β t =
      (Emain θ β X - mainPsi θ β X / Real.log X) - (Emain θ β Y - mainPsi θ β Y / Real.log Y) := by sorry
