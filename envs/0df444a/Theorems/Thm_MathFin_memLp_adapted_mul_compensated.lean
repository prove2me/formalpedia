-- Prove2me | Theorems.Thm_MathFin_memLp_adapted_mul_compensated
-- name    : MathFin.memLp_adapted_mul_compensated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:33:33.641539+00:00
-- url     : https://prove2.me/theorems/2d1762f6-7c8f-4e92-8b19-62886717188b
-- title:
--   memLp adapted mul compensated
-- statement:
--   The source theorem `MathFin.memLp_adapted_mul_compensated` is extracted from `MathFin.Foundations.PoissonCompensatedIsometryAdapted`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F001

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# The compensated-Poisson isometry kernel (increment-independence cornerstone)

The jump analogue of `Foundations/ItoIsometryAdapted.lean`. For a Poisson random measure `N`,
the second-moment energy identities that the Itô–Lévy isometry sums are:

* diagonal `𝔼[φ² · Ñ(box)²] = 𝔼[φ²] · ν̂(box)` (`integral_adapted_sq_mul_compensated_sq`);
* cross `𝔼[φ · Ñ(box₁) · ψ · Ñ(box₂)] = 0` for disjoint boxes with `box₁` in the past-region
  of `box₂` (`integral_cross_compensated_eq_zero`).

Both flow from the single structure field `indep_of_disjoint_region` (independent scattering):
`N` on any region disjoint from `D` is independent of `N(·, D)`. The past `σ`-algebra at a time
`s` and the count on any box disjoint from a future box both live in that "disjoint region", so
one field closes every cross-term — the different-time cross pairs *and* the same-time /
different-mark cross pairs that a `time × mark` simple integrand produces.

## Provenance

Design mirrors our continuous `ItoIsometryAdapted`; the PRM object is from
`Foundations/PoissonRandomMeasure` (field shape consulted from `cgarryZA/LevyStochCalc`, cited).
The isometry content is our own — LevyStochCalc states it as cited axiom #6.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The past and disjoint-region `σ`-algebras -/

/-! ### Measurability of adapted integrands and compensated increments -/

/-! ### The independence cornerstone and the energy identities -/

theorem _root_.MathFin.memLp_adapted_mul_compensated (N : PoissonRandomMeasure P ν) {s t : ℝ}
    {A : Set E} (hA : MeasurableSet A) (hAfin : ν A ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) (hφL2 : MemLp φ 2 P) :
    MemLp (fun ω => φ ω * N.compensated (Set.Ioc s t ×ˢ A) ω) 2 P := by sorry
