-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_span_eq_top_of_forall_dot_eq_zero
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.span_eq_top_of_forall_dot_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:36:42.361455+00:00
-- url     : https://prove2.me/theorems/4eebbcde-feeb-4b65-86be-077e0ba1b58f
-- title:
--   Par: span eq top of forall dot eq zero
-- statement:
--   The Par construction uses the span eq top of forall dot eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SpanEqTopOfForallDotEqZero.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SpanEqTopOfForallDotEqZero.lean#L14-L34

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.span_eq_top_of_forall_dot_eq_zero (S : Set (Fin m → ℂ))
    (hS : ∀ v : Fin m → ℂ, (∀ w ∈ S, ∑ j, v j * w j = 0) → v = 0) :
    Submodule.span ℂ S = ⊤ := by sorry
