-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_tendsto_eLpNorm_profileExpVector_sub
-- name    : LevyStochCalc.Poisson.tendsto_eLpNorm_profileExpVector_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:02:49.925184+00:00
-- url     : https://prove2.me/theorems/f1360ff4-8286-452b-9102-1cf7c2e33ac5
-- title:
--   tendsto eLpNorm profileExpVector sub
-- statement:
--   The source theorem `LevyStochCalc.Poisson.tendsto_eLpNorm_profileExpVector_sub` is extracted from `LevyStochCalc.Poisson.ProfileExpVectorCont`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F001
import Definitions.Def_LevyStochCalc_Poisson_ProfileExpVector_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F002
import Definitions.Def_LevyStochCalc_Probability_L2Series_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuity of the exponential vector of a step in the mark profile

For a Poisson random measure with intensity `ν`, a step `(a, b]` and a real frequency `u`, the
exponential vector `𝓔_u(f) = exp (i u J(f)) · exp (−(b − a) ∫ ψ_u(f) dν)` of the step at a
square-integrable mark profile `f` depends continuously on `f`: if `f_n → f` in `L²(ν)` then
`𝓔_u(f_n) → 𝓔_u(f)` in `L²(P; ℂ)`. The compensated integrals converge in `L²(P)` by the isometry,
so their characters converge in `L²(P)` because `x ↦ e^{iux}` is `|u|`-Lipschitz, and the
deterministic factors converge because the Lévy characteristic exponent is continuous along
`L²(ν)` convergence.

The same Lipschitz bound `|e^{iux} − e^{iuy}| ≤ |u| |x − y|` makes `e^{iu f_n} − 1 → e^{iu f} − 1`
in `L²(ν; ℂ)`, whence the two constants
`∫ ‖e^{iu f} − 1‖ ^ 2 dν` and `∫ (e^{iu f} − 1) ^ 2 dν` are continuous along `L²(ν)` convergence.

## Main statements

* `LevyStochCalc.Poisson.tendsto_eLpNorm_profileExpVector_sub` — `𝓔_u(f_n) → 𝓔_u(f)` in
  `L²(P; ℂ)`.
* `LevyStochCalc.Poisson.tendsto_eLpNorm_exp_I_mul_sub_one_sub` — `e^{iu f_n} − 1 → e^{iu f} − 1`
  in `L²(ν; ℂ)`.
* `LevyStochCalc.Poisson.tendsto_integral_norm_sq_exp_I_mul_sub_one` —
  `∫ ‖e^{iu f_n} − 1‖ ^ 2 dν → ∫ ‖e^{iu f} − 1‖ ^ 2 dν`.
* `LevyStochCalc.Poisson.tendsto_integral_sq_exp_I_mul_sub_one` —
  `∫ (e^{iu f_n} − 1) ^ 2 dν → ∫ (e^{iu f} − 1) ^ 2 dν`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem _root_.LevyStochCalc.Poisson.tendsto_eLpNorm_profileExpVector_sub (N : PoissonRandomMeasure P ν) {h : ℕ → E → ℝ}
    {f : E → ℝ} (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => profileExpVector N (h n) a b u ω
      - profileExpVector N f a b u ω) 2 P) atTop (𝓝 0) := by sorry
