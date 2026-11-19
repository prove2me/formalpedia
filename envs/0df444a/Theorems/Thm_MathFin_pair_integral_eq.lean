-- Prove2me | Theorems.Thm_MathFin_pair_integral_eq
-- name    : MathFin.pair_integral_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:37:10.148085+00:00
-- url     : https://prove2.me/theorems/c4e53369-fedc-443a-91bf-7a2773dfc157
-- title:
--   pair integral eq
-- statement:
--   The source theorem `MathFin.pair_integral_eq` is extracted from `MathFin.Foundations.PoissonCompensatedIntegralOperator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIntegralOperator_F000

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# The compensated-Poisson integral operator on marked simple integrands

The two linear maps out of the marked simple-integrand module `levySimpleModule`, mirroring the
continuous `ItoIntegralL2.itoAssembly` / `simpleAssembly`:

* `intAssembly : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 P` — the elementary compensated integral
  `∑_b φ_b · Ñ(box b)`, viewed in `L²(P)`;
* `emb : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 (P.prod (referenceIntensity ν))` — the integrand
  `∑_b φ_b · 𝟙_{box b}`, viewed in `L²(dP ⊗ dν̂)` (the sibling module).

The `L²` isometry `‖intAssembly V‖ = ‖emb V‖`, obtained by summing the overlapping-box bilinear
pairing `integral_bilinear_pairing`, and the `extendOfNorm` CLM are built on these.

## Provenance

Mirrors the continuous `ItoIntegralL2` assembly; the compensated-integral content is our own.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The elementary compensated integral as a linear map -/

/-! ### The integrand embedding into the predictable `L²(dP ⊗ dν̂)` -/

/-! ### The isometry `‖intAssembly V‖ = ‖emb V‖` (summing the bilinear pairing) -/

theorem _root_.MathFin.pair_integral_eq (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
          * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P
      = ∫ p, (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
              * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
          ∂(P.prod (referenceIntensity ν)) := by sorry
