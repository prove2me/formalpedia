-- Prove2me | Theorems.Thm_GlobalTheory_valuation_sqrt_absNorm_eq_one
-- name    : GlobalTheory.valuation_sqrt_absNorm_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:40.909096+00:00
-- url     : https://prove2.me/theorems/91e08d8c-8c1f-4105-b856-298e222f2592
-- title:
--   Global Theory: valuation sqrt abs Norm eq one
-- statement:
--   The Global Theory construction uses the valuation sqrt abs Norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationSqrtAbsNormEqOne.lean#L6-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationSqrtAbsNormEqOne.lean#L6-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationSqrtAbsNormEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.valuation_sqrt_absNorm_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
        A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by sorry
