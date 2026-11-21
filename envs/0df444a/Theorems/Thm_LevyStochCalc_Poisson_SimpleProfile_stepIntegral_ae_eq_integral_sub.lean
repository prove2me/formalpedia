-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_SimpleProfile_stepIntegral_ae_eq_integral_sub
-- name    : LevyStochCalc.Poisson.SimpleProfile.stepIntegral_ae_eq_integral_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:19:21.372653+00:00
-- url     : https://prove2.me/theorems/3c035efa-292a-4f68-b140-821df81867fb
-- title:
--   stepIntegral ae eq integral sub
-- statement:
--   The source theorem `LevyStochCalc.Poisson.SimpleProfile.stepIntegral_ae_eq_integral_sub` is extracted from `LevyStochCalc.Poisson.CompensatedProfileRaw`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileRaw_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of an integrable mark profile is pathwise

Let `N` be a Poisson random measure on `[0, ∞) × E` with `σ`-finite intensity `ν`, possibly
`ν(E) = ∞`, and let `f ∈ L¹(ν) ∩ L²(ν)` be a deterministic mark profile. Over a step `(a, b]`,
`0 ≤ a ≤ b`, almost surely `f` is integrable on `(a, b] × E` against `N(ω)` and the compensated
integral of `f` is the raw integral minus its compensator:

  `∫_E f(e) ΔÑ(de) = ∫_{(a, b] × E} f(e) N(ω)(ds, de) − (b − a) ∫_E f dν`.

The mean measure of `N` is its reference intensity (Campbell's formula), so the raw integral of
`|f|` over the step has mean `(b − a) ‖f‖_{L¹(ν)}`. At a simple profile the identity is the
definition of the compensated step integral. Simple functions converging to `f` both in `L¹(ν)`
and in `L²(ν)` then carry the identity to `f`: the compensated integrals converge in `L²(P)` and
the raw integrals minus their compensators converge in `L¹(P)`.

## Main statements

* `LevyStochCalc.Poisson.PoissonRandomMeasure.bind_N` — the mean measure of a Poisson random
  measure is its reference intensity.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.lintegral_lintegral_N` — Campbell's formula.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.ae_integrableOn_cell` — an integrable mark profile
  is almost surely integrable on a step times the mark space.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_integral_sub` — the compensated integral of a
  mark profile in `L¹(ν) ∩ L²(ν)` is the raw integral minus its compensator.
* `LevyStochCalc.Poisson.compensatedProfileRepr_ae_eq_integral_sub` — the same for the
  representative of the compensated integral for a sub-σ-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The mean measure -/

namespace PoissonRandomMeasure

variable (N : PoissonRandomMeasure P ν)

end PoissonRandomMeasure

/-! ### Simple profiles -/

theorem _root_.LevyStochCalc.Poisson.SimpleProfile.stepIntegral_ae_eq_integral_sub (N : PoissonRandomMeasure P ν)
    (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) {b : ℝ} (hab : a ≤ b) :
    G.stepIntegral N a b =ᵐ[P] fun ω =>
      (∫ q in Set.Ioc a b ×ˢ Set.univ, G.toFun q.2 ∂(N.N ω)) - (b - a) * ∫ e, G.toFun e ∂ν := by sorry
