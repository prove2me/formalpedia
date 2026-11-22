-- Prove2me | Theorems.Thm_GRH_primitive_nonprincipal_fourth_power_ramp_window_certificates
-- name    : GRH.primitive_nonprincipal_fourth_power_ramp_window_certificates
-- status  : Open
-- author  : @GeorgeCoote
-- created : 2026-11-21T17:05:14.550188+00:00
-- url     : https://prove2.me/theorems/eb89fe98-c71f-43f5-80e4-ae751988388e
-- title:
--   Cofinal fourth-power certificates for primitive character ramps
-- statement:
--   Fix a primitive nonprincipal Dirichlet character $\chi$ and an exponent $1/2<\theta\le 0.8749570698$. Define its corrected prime ramp by
--
--   $$
--   G_\chi(x)=\sum_{1\le n\le x}\Lambda(n)\operatorname{Re}\chi(n)\,(x/n-1)_+
--   +x\operatorname{Re}\frac{L'(1,\chi)}{L(1,\chi)}.
--   $$
--
--   There exist $\delta>0$ and $C\ge 0$ such that for arbitrarily large positive integers $K$, we have $G_\chi(j^4)\le C(j^4)^\theta$ whenever $j\ge K$ and $(j-1)^4\le\lfloor (K^4)^{1+\delta}\rfloor+1$. The final sample supplies the right endpoint of the last interpolation interval.
-- source:
--   Sparse sampling of the integer-knot certificates in https://prove2.me/theorems/bcdc1c37-1d9b-4169-9472-b95a87c49451.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Order.Interval.Finset.Nat

open Finset ArithmeticFunction Set

namespace GRH

theorem primitive_nonprincipal_fourth_power_ramp_window_certificates :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ θ : ℝ, 1/2 < θ → θ ≤ (0.8749570698:ℝ) → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ K₀ : ℕ, ∃ K : ℕ, K₀ ≤ K ∧ 1 ≤ K ∧
          ∀ j : ℕ, K ≤ j → (j-1)^4 ≤ ⌊((K^4 : ℕ):ℝ)^(1+δ)⌋₊+1 →
          let k := j^4
          (∑ n ∈ range (k+1), vonMangoldt n * (χ (n:ZMod q)).re *
            max ((k:ℝ)/(n:ℝ)-1) 0) +
            (k:ℝ) * (deriv χ.LFunction 1 / χ.LFunction 1).re ≤ C*(k:ℝ)^θ := by sorry

end GRH
