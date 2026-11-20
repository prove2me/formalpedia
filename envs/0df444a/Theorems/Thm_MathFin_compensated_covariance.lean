-- Prove2me | Theorems.Thm_MathFin_compensated_covariance
-- name    : MathFin.compensated_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:34:26.917183+00:00
-- url     : https://prove2.me/theorems/5f45a63c-98d9-4a49-a9e9-bc05105ae4e4
-- title:
--   compensated covariance
-- statement:
--   The source theorem `MathFin.compensated_covariance` is extracted from `MathFin.Foundations.PoissonCompensatedBilinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F000

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

theorem _root_.MathFin.compensated_covariance (N : PoissonRandomMeasure P ν) {C D : Set (ℝ × E)}
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤) :
    ∫ ω, N.compensated C ω * N.compensated D ω ∂P = (referenceIntensity ν (C ∩ D)).toReal := by sorry
