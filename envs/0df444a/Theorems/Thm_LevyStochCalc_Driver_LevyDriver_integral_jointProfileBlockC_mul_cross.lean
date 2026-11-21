-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_jointProfileBlockC_mul_cross
-- name    : LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_cross
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:08:00.930876+00:00
-- url     : https://prove2.me/theorems/edfbe6dc-2d6c-490c-8508-e9f89d2ecd1f
-- title:
--   integral jointProfileBlockC mul cross
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_cross` is extracted from `LevyStochCalc.Driver.JointChaosProfileExpansion`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfileExpansion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos expansion of the exponential vector of a step at a mark profile

For a Lévy driver, a coordinate `j`, a step `(a, b]` with `τ = b − a`, a finite pairwise disjoint
family `A` of mark sets of finite intensity, a Brownian frequency `α` and a complex profile `c`
constant on each mark set, the block of total degree `e` of the step is

  `C_e(α, c; A) = ∑_(r + s = e) ((i α) ^ r / r!) H_r(ΔWʲ; τ) (D_s(c) / s!)`,

a combination of the complex joint chaos elements of the bidegrees `(r, s)` with `r + s = e`.
Through the bidegree Gram across families and the binomial identity
`∑_(r + s = e) x ^ r y ^ s / (r! s!) = (x + y) ^ e / e!`, blocks of different total degree are
orthogonal whatever the two families, and

  `E[C_e(α, c; A) C_e(α', c'; A')] = (τ (⟨c, c'⟩ − α α')) ^ e / e!`,
  `E‖C_e(α, c; A)‖ ^ 2 = (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k))) ^ e / e!`,

with `⟨c, c'⟩ = ∑_(k, l) c_k c'_l ν(A k ∩ A' l)`. The blocks are the Cauchy product of the Wiener
chaos series of the increment, absolutely summable everywhere, and the chaos series of the strips,
absolutely summable almost everywhere, so they sum almost everywhere, and by the summability of
their `L²` norms in `L²(P; ℂ)`, to the joint exponential vector `V_W(α) V_N(c; A)`, the product of
the exponential vector of the increment and that of the strips; its second moment is
`exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`. At `c_k = e^{i u h_k} − 1` for a simple mark profile `h`
the joint exponential vector is almost surely `V_W(α) 𝓔_u(h)`, with `𝓔_u(h)` the exponential vector
of the step at `h`, and the constants of the block moments are
`∫ ‖e^{i u h} − 1‖ ^ 2 dν` and `∫ (e^{i u h} − 1) ^ 2 dν`. The product `V_W(α) 𝓔_u(h)` depends
continuously on `h ∈ L²(ν)`, as the first factor is bounded.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC` — the block of total degree `e`.
* `LevyStochCalc.Driver.LevyDriver.jointProfileExpVector` — the joint exponential vector.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_cross`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_conj_cross` — the block Gram
  across two mark families.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileBlockC`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_sq` — the two second moments.
* `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_zero`,
  `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_one` — the blocks of total degree zero and
  one, `1` and `i α ΔWʲ + ∑_k c_k Ñ((a, b] ×ˢ A k)`.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileBlockC_simpleProfile`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_sq_simpleProfile` — the second
  moments at `c_k = e^{i u h_k} − 1` through `∫ ‖e^{i u h} − 1‖ ^ 2 dν` and
  `∫ (e^{i u h} − 1) ^ 2 dν`.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointProfileBlockC_mul_conj` — the pairing
  of blocks against a coefficient measurable at the node preceding the step.
* `LevyStochCalc.Driver.LevyDriver.hasSum_jointProfileBlockC` — the blocks sum almost everywhere
  to the joint exponential vector.
* `LevyStochCalc.Driver.LevyDriver.hasSum_toLp_jointProfileBlockC` — the same in `L²(P; ℂ)`.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileExpVector` —
  `E‖V_W(α) V_N(c; A)‖ ^ 2 = exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`.
* `LevyStochCalc.Driver.LevyDriver.jointProfileExpVector_ae_eq` — at `c_k = e^{i u h_k} − 1` the
  joint exponential vector is `V_W(α) 𝓔_u(h)`.
* `LevyStochCalc.Driver.LevyDriver.hasSum_toLp_jointProfileBlockC_simpleProfile` — the blocks
  sum in `L²(P; ℂ)` to `V_W(α) 𝓔_u(h)`.
* `LevyStochCalc.Driver.LevyDriver.tendsto_eLpNorm_wienerExpVector_mul_profileExpVector_sub` —
  `V_W(α) 𝓔_u(h)` is continuous in `h` from `L²(ν)` to `L²(P; ℂ)`.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
  Filter
open scoped NNReal ENNReal Topology

universe u v w

section Expansion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Blocks of a total degree -/

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_cross (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (α α' : ℝ) (c : Fin p → ℂ) (c' : Fin q → ℂ) (e e' : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b A α c e ω * D.jointProfileBlockC j a b A' α' c' e' ω ∂P
      = if e = e' then ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A' l)).toReal : ℂ) - (α : ℂ) * α')) ^ e
          / (e.factorial : ℂ) else 0 := by sorry
