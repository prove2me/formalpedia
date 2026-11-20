-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Martingale_brownianMotion_sq_integrable
-- name    : LevyStochCalc.Brownian.Martingale.brownianMotion_sq_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T14:53:50.207808+00:00
-- url     : https://prove2.me/theorems/e010d4a4-a0e3-4252-ab39-6fb6e3a302fc
-- title:
--   brownianMotion sq integrable
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Martingale.brownianMotion_sq_integrable` is extracted from `LevyStochCalc.Brownian.Martingale`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Continuity_F000
import Definitions.Def_LevyStochCalc_Brownian_Continuity_F001
import Definitions.Def_LevyStochCalc_Brownian_Continuity_F002
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Natural filtration, martingale property, quadratic variation

Brownian motion `W` generates the *natural filtration*

  `ℱ_t := σ(W_s : s ≤ t)`,

w.r.t. which `W` is a martingale, and has *quadratic variation*

  `⟨W⟩_t = t`.

The quadratic-variation identity `(dW)² = dt` is the cornerstone of the Itô
formula; without it the second-order Taylor term in the diffusion case would
not produce the `½ σ² f''` correction.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §1.5 + §3.1.

## Proof structure

1. Construct `naturalFiltration W` via `MeasureTheory.Filtration.natural`.
2. Adaptedness is automatic via `MeasureTheory.Filtration.stronglyAdapted_natural`.
3. Conditional-expectation identity: `𝔼[W_t | ℱ_s] = W_s` reduces to
   `𝔼[W_t − W_s | ℱ_s] = 0`. This requires:
   * **σ-algebra independence**: `σ(W_t − W_s) ⊥⊥ ℱ_s` under `P`. This is the
     structure field `BrownianMotion.joint_increment_independent`, read through
     the description of `naturalFiltration W` at `s` as `⨆ j ∈ Set.Iic s, σ(W_j)`;
     it is stronger than the derived pairwise statement
     `BrownianMotion.increment_independent`.
   * **Mean zero of increment**: `𝔼[W_t − W_s] = ∫ x, x ∂(gaussianReal 0 ⟨t-s⟩) = 0`
     by `ProbabilityTheory.integral_id_gaussianReal`.
   * **`condExp_indep_eq`**: independence + measurability ⇒ `𝔼[X | ℱ] = 𝔼[X]` a.s.

## Downstream modules

The conditional-expectation identities for Brownian increments live in
`LevyStochCalc.Brownian.MartingaleCondExp`, the martingale property and the quadratic variation
`⟨W⟩_t = t` in `LevyStochCalc.Brownian.MartingaleQuadVar`, and their counterparts for the
right-continuation of the natural filtration in `LevyStochCalc.Brownian.MartingaleRightCont`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section Moments
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Martingale.brownianMotion_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.Integrable (fun ω => (W.W s ω)^2) P := by sorry
