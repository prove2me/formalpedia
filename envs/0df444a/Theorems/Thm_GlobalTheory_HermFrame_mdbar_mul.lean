-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_mdbar_mul
-- name    : GlobalTheory.HermFrame.mdbar_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:38:47.529141+00:00
-- url     : https://prove2.me/theorems/7efa9ee5-22ec-4a54-b461-fd04a1b7b225
-- title:
--   Herm Frame: mdbar mul
-- statement:
--   The Herm Frame construction uses the mdbar mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L222-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L222-L229

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}

theorem GlobalTheory.HermFrame.mdbar_mul [Fintype n] {B : E → Matrix n l ℂ} (h : MContDiffAt 1 A z)
    (h' : MContDiffAt 1 B z) (ξ : E) :
    mdbar (fun x => A x * B x) z ξ = A z * mdbar B z ξ + mdbar A z ξ * B z := by sorry
