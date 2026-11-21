-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_exists_simpleProfile_tendsto_L2
-- name    : LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T10:33:49.114145+00:00
-- url     : https://prove2.me/theorems/5b7279ca-c231-4c89-8a0e-4af97e851a0e
-- title:
--   exists simpleProfile tendsto L2
-- statement:
--   The source theorem `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` is extracted from `LevyStochCalc.Poisson.SimpleProfile`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple mark profiles and their compensated step integrals

A *simple mark profile* for an intensity `ν` on the mark space is a finite family of pairwise
disjoint mark sets of finite intensity carrying constant coefficients, `∑ₖ cₖ 𝟙_{Bₖ}`. Every
square-integrable mark profile is the `L²(ν)` limit of simple profiles, obtained from the nonzero
level sets of square-integrable simple functions approximating it in `L²(ν)`; a bounded one is
the limit of simple profiles obeying the same bound, obtained from the simple functions
approximating it inside the interval the bound cuts out.

The compensated integral of a simple profile over the step `(a, b]` is
`∑ₖ cₖ Ñ((a, b] × Bₖ)`. The `L²(P)` pairing of two such integrals over a common step is
`(b − a) ∫ f g dν`, so profiles converging in `L²(ν)` have compensated integrals converging in
`L²(P)`.

## Main definitions

* `LevyStochCalc.Poisson.SimpleProfile` — a simple mark profile.
* `LevyStochCalc.Poisson.SimpleProfile.toFun` — the function it carries.
* `LevyStochCalc.Poisson.SimpleProfile.stepIntegral` — its compensated integral over a step.

## Main statements

* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2_of_memLp` — approximation of a
  square-integrable mark profile by simple profiles.
* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` — approximation of a bounded
  square-integrable mark profile by simple profiles obeying the same bound.
* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` — the `L²(P)` pairing of two
  compensated step integrals.
* `LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub` — the isometry
  `‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`.
* `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` — convergence of the compensated
  integrals in `L²(P)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

/-! ### The compensated integral of a simple profile over a step -/

variable (N : PoissonRandomMeasure P ν)

/-! ### Simple profiles from simple functions -/

end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

omit [SigmaFinite ν] in

theorem _root_.LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2 {f : E → ℝ} (hf : MemLp f 2 ν) {Cb : ℝ}
    (hb : ∀ e, |f e| ≤ Cb) :
    ∃ G : ℕ → SimpleProfile E ν, (∀ n e, |(G n).toFun e| ≤ Cb) ∧
      Filter.Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν)
        Filter.atTop (nhds 0) := by sorry
