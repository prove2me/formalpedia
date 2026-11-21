-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_compensatedProfile_finsetSum_smul
-- name    : LevyStochCalc.Poisson.compensatedProfile_finsetSum_smul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:06:57.966407+00:00
-- url     : https://prove2.me/theorems/32f50ec9-09e4-4aa7-a156-6053e8028821
-- title:
--   compensatedProfile finsetSum smul
-- statement:
--   The source theorem `LevyStochCalc.Poisson.compensatedProfile_finsetSum_smul` is extracted from `LevyStochCalc.Poisson.CompensatedProfileLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileLinear_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the compensated integral of a mark profile

For the compensated integral `J(f)` over the step `(a, b]` of a mark profile `f : E → ℝ` against a
Poisson random measure with intensity `ν`, and square-integrable profiles `f₁, …, fₙ`,

  `J(∑ᵢ cᵢ fᵢ) = ∑ᵢ cᵢ J(fᵢ)`   almost surely.

The defect `X = J(∑ᵢ cᵢ fᵢ) − ∑ᵢ cᵢ J(fᵢ)` is orthogonal in `L²(P)` to the compensated integral
of every square-integrable profile, because the `L²(P)` pairing
`E[J(f) J(g)] = (b − a) ∫ f g dν` is linear in `f`. The defect is itself a combination of such
integrals, so its second moment vanishes.

The compensated integral depends on the profile only through its class modulo `ν`-null sets:
the approximating sequences of simple profiles, and hence the defining limit, are the same for
two profiles equal `ν`-almost everywhere.

## Main statements

* `LevyStochCalc.Poisson.compensatedProfile_congr_ae` — profiles equal `ν`-almost everywhere
  have the same compensated integral over every step.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_of_ae_eq` — the same, almost surely.
* `LevyStochCalc.Poisson.compensatedProfile_finsetSum_smul` — the compensated integral of a
  finite linear combination of square-integrable profiles.
* `LevyStochCalc.Poisson.compensatedProfile_finsetSum` — of a finite sum.
* `LevyStochCalc.Poisson.compensatedProfile_add`, `LevyStochCalc.Poisson.compensatedProfile_smul`,
  `LevyStochCalc.Poisson.compensatedProfile_neg`, `LevyStochCalc.Poisson.compensatedProfile_sub`
  — of a sum, a scalar multiple, a negative and a difference.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Congruence -/

/-! ### Linear combinations -/

theorem _root_.LevyStochCalc.Poisson.compensatedProfile_finsetSum_smul (N : PoissonRandomMeasure P ν) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) {f : ι → E → ℝ} (hf : ∀ i ∈ s, MemLp (f i) 2 ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (∑ i ∈ s, c i • f i) a b
      =ᵐ[P] ∑ i ∈ s, c i • compensatedProfile N (f i) a b := by sorry
