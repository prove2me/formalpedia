-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_IsSesq_polarisation
-- name    : GlobalTheory.HermFrame.IsSesq.polarisation
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:46.7866+00:00
-- url     : https://prove2.me/theorems/60d6969f-5e68-4a09-ab3e-f9d701a93355
-- title:
--   Is Sesq: polarisation
-- statement:
--   The Is Sesq construction uses the polarisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L280-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L280-L286

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.HermFrame.IsSesq.polarisation {F : V → V → M} (hF : IsSesq F) (x y : V) :
    F x y = (1 / 4 : ℂ) • ((F (x + y) (x + y) + (-1 : ℂ) • F (x - y) (x - y)) +
      (I • F (x + I • y) (x + I • y) + (-I) • F (x - I • y) (x - I • y))) := by sorry
