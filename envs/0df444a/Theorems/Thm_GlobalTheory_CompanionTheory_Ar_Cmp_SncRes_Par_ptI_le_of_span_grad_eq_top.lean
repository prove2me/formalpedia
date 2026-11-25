-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_ptI_le_of_span_grad_eq_top
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.ptI_le_of_span_grad_eq_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:26:53.211739+00:00
-- url     : https://prove2.me/theorems/85e01784-fc5f-5e4c-a368-fcb1f06172fa
-- title:
--   Par: pt I le of span grad eq top
-- statement:
--   The Par construction uses the pt I le of span grad eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SpanEqTopOfForallDotEqZero.lean#L44-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SpanEqTopOfForallDotEqZero.lean#L44-L75

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SpanEqTopOfForallDotEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing
variable {m : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.ptI_le_of_span_grad_eq_top (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) (A : Set (MvPolynomial (Fin m) ℂ)) (hAJ : A ⊆ J)
    (hA0 : ∀ a ∈ A, eval t a = 0) (hA : Submodule.span ℂ (gradP t '' A) = ⊤) :
    ptI t ≤ J := by sorry
