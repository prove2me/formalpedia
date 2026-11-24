-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_orthLift
-- name    : GlobalTheory.HermFrame.form_orthLift
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:30.390819+00:00
-- url     : https://prove2.me/theorems/8cd5ae9a-d2a3-460d-b88f-42c51b9da24c
-- title:
--   Herm Frame: form orth Lift
-- statement:
--   The Herm Frame construction uses the form orth Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L402-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L402-L406

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
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem GlobalTheory.HermFrame.form_orthLift (hu : IsUnit (subGram H).det) (q q' : l → ℂ) :
    form H (orthLift H *ᵥ q) (orthLift H *ᵥ q') = form (quotGram H) q q' := by sorry
