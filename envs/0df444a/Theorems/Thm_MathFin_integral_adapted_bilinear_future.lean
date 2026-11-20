-- Prove2me | Theorems.Thm_MathFin_integral_adapted_bilinear_future
-- name    : MathFin.integral_adapted_bilinear_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:35:14.168732+00:00
-- url     : https://prove2.me/theorems/b5ddae3a-14ae-4787-b305-897b0f04e613
-- title:
--   integral adapted bilinear future
-- statement:
--   The source theorem `MathFin.integral_adapted_bilinear_future` is extracted from `MathFin.Foundations.PoissonCompensatedBilinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F001

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# The compensated Poisson random measure is an orthogonal martingale measure

The diagonal second moment `𝔼[Ñ(B)²] = ν̂(B)` (`compensated_integral_sq`) is the `C = D` case of the
full **covariance** of the compensated Poisson random measure:

  `𝔼[Ñ(C)·Ñ(D)] = ν̂(C ∩ D)`   for measurable finite-intensity `C, D`.

`Ñ` is thus an *orthogonal martingale measure* with (deterministic) intensity `ν̂`: increments on
disjoint regions are uncorrelated, and the covariance of general increments is the intensity of their
overlap. The proof decomposes `C = (C∩D) ⊔ (C\D)` and `D = (C∩D) ⊔ (D\C)` into three disjoint pieces
whose counts are independent (the independent-scattering field `indep_of_disjoint_region`); the three
disjoint cross-pairs vanish (`integral_mul_compensated_eq_zero`) and the diagonal `𝔼[Ñ(C∩D)²]` is
`ν̂(C∩D)`.

This covariance is the bilinear core the compensated-integral isometry is built on (the jump analogue
of `WienerIntegralL2.covariance_increment_aux`), and the first rung of the Itô–Lévy integral
*operator* (the CLM over the characterised predictable `L²`).

## Provenance

Built on our own `PoissonRandomMeasure` / `PoissonCompensatedIsometryAdapted` (PRM field shape
consulted from `cgarryZA/LevyStochCalc`, Apache-2.0, cited — a rendering of Applebaum 2009 Def.
2.3.1; the proofs are ours). Reference: Applebaum, *Lévy Processes and Stochastic Calculus*, CUP
2009, Thm 4.2.3.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Weighted future pairings — the bilinear rung

The covariance above is the `φ ≡ 1` case of a **weighted** future pairing
`𝔼[φ · Ñ(C) · Ñ(D)] = 𝔼[φ] · ν̂(C ∩ D)` for `φ` adapted at a time `s` before both `C, D`
(`C, D ⊆ (s, ∞) × E`). It is the jump analogue of `ItoIsometryAdapted.rect_increment_pairing`
(Brownian rectangles — cited, not reused): the past-adapted weight factors out of every future
increment, and the increment covariance supplies `ν̂(C ∩ D)`. From it, splitting a box at the later
of two start times gives the **overlapping-box bilinear pairing** the Itô–Lévy isometry sums over.

All of it rests on the *single-increment* field `indep_of_disjoint_region` — no past-vs-future
`σ`-algebra independence is assumed. Integrability of the triple products is bought by the same
independence (a past-adapted factor is `⟂` any future increment it multiplies). -/

theorem _root_.MathFin.integral_adapted_bilinear_future (N : PoissonRandomMeasure P ν) {s : ℝ}
    {C D : Set (ℝ × E)} (hCms : MeasurableSet C) (hDms : MeasurableSet D)
    (hCsub : C ⊆ Set.Ioi s ×ˢ Set.univ) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) (hφint : Integrable φ P) :
    ∫ ω, φ ω * N.compensated C ω * N.compensated D ω ∂P
      = (∫ ω, φ ω ∂P) * (referenceIntensity ν (C ∩ D)).toReal := by sorry
