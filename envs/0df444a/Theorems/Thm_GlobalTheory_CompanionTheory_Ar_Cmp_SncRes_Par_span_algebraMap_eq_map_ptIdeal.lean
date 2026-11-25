-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_span_algebraMap_eq_map_ptIdeal
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.span_algebraMap_eq_map_ptIdeal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:36:43.112805+00:00
-- url     : https://prove2.me/theorems/ecd1056c-fd33-4ff1-8b2e-4712ea1a404b
-- title:
--   Par: span algebra Map eq map pt Ideal
-- statement:
--   The Par construction uses the span algebra Map eq map pt Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SpanEqTopOfForallDotEqZero.lean#L97-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SpanEqTopOfForallDotEqZero.lean#L97-L184

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.span_algebraMap_eq_map_ptIdeal (e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : Fin e → MvPolynomial (Fin m) ℂ) (hI : ∀ h ∈ I, eval t h = 0) (hr : ∀ l, eval t (r l) = 0)
    (hv : ∀ v : Fin m → ℂ, (∀ h ∈ I, ∑ j, v j * eval t (pderiv j h) = 0) →
      (∀ l, ∑ j, v j * eval t (pderiv j (r l)) = 0) → v = 0) :
    Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) := by sorry
