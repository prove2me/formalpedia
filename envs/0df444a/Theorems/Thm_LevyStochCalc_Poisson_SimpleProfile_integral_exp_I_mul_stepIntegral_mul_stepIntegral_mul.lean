-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_SimpleProfile_integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul
-- name    : LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:24:26.750043+00:00
-- url     : https://prove2.me/theorems/3fed0029-5fef-440d-aa98-98f6be816503
-- title:
--   integral exp I mul stepIntegral mul stepIntegral mul
-- statement:
--   The source theorem `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul` is extracted from `LevyStochCalc.Poisson.ProfileExpPairingSimple`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated step integral against first- and second-order elements

For a simple mark profile with pairwise disjoint mark sets `B_k` of finite intensity, the
compensated counts `Ñ_k` of the strips `(a, b] × B_k` are independent, so the character
`e^{iuJ_c}` of the compensated step integral `J_c = ∑_k c_k Ñ_k` carried by a coefficient vector
`c` factors over the strips. Each factor pairs with `Ñ_k` and `Ñ_k²` through the identities of
`Poisson/CompensatedCountCharacter.lean`, with `λ_k = (b − a) ν(B_k)`:
`E[e^{isÑ} Ñ] = λ (e^{is} − 1) E[e^{isÑ}]` and
`E[e^{isÑ} Ñ²] = (λ² (e^{is} − 1)² + λ e^{is}) E[e^{isÑ}]`. Summing over the strips gives, for
coefficient vectors `d, d'` on the same mark sets and `γ_k = e^{iuc_k} − 1`,

  `E[e^{iuJ_c} J_d] = (b − a) ∑_k ν(B_k) γ_k d_k · E[e^{iuJ_c}]`,

and the matching second-order identity for `E[e^{iuJ_c} J_d J_{d'}]`. On a common refinement of
finitely many simple profiles these become the pairings of the character of the compensated
integral of one simple profile `G` with the compensated integrals of others, with
`γ = e^{iuG} − 1`:

  `E[e^{iuJ(G)} J(F)] = (b − a) ∫ γ F dν · E[e^{iuJ(G)}]`,
  `E[e^{iuJ(G)} J(F) J(K)]`
  `  = ((b − a)² ∫ γ F dν ∫ γ K dν + (b − a) (∫ γ F K dν + ∫ F K dν)) · E[e^{iuJ(G)}]`.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul` —
  the first- and second-order pairings on the mark sets of one simple profile.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul_mul` — the
  first- and second-order pairings at simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.abs_toFun_le` — the function of a simple profile is bounded
  by the sum of the absolute values of its coefficients.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Strips of a simple profile -/

namespace SimpleProfile

/-! ### Pairings on the mark sets of one simple profile -/

theorem _root_.LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c d d' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * (((H.withCoeff d).stepIntegral N a b ω : ℝ) : ℂ)
        * (((H.withCoeff d').stepIntegral N a b ω : ℝ) : ℂ) ∂P
      = (((b - a : ℝ) : ℂ) ^ 2 * (∑ k, ((ν (H.B k)).toReal : ℂ)
            * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1) * (d k : ℂ)))
          * (∑ k, ((ν (H.B k)).toReal : ℂ)
            * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1) * (d' k : ℂ)))
          + ((b - a : ℝ) : ℂ) * ((∑ k, ((ν (H.B k)).toReal : ℂ)
            * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1) * (d k : ℂ) * (d' k : ℂ)))
            + ∑ k, ((ν (H.B k)).toReal : ℂ) * ((d k : ℂ) * (d' k : ℂ))))
        * ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          ∂P := by sorry
