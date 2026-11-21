-- Prove2me | Theorems.Thm_MasulloRH_prime_ramp_chord_and_fourth_power_bound
-- name    : MasulloRH.prime_ramp_chord_and_fourth_power_bound
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:42:21.148925+00:00
-- url     : https://prove2.me/theorems/79af092f-5dbc-45d7-9206-d7a784591316
-- title:
--   The corrected prime ramp on fourth-power intervals is controlled by its two endpoint values
-- statement:
--   Let G(y) be the corrected von Mangoldt prime ramp, Σ_{n≤y} Λ(n)(y/n−1)₊ − y(log y−1−γ). For 0<a≤b and y=(1−t)a+tb with 0≤t≤1, one has G(y)≤(1−t)G(a)+tG(b)+t(1−t)(b−a)²/y. In particular, for k≥1, 1/2≤θ≤1 and C≥0, bounds G(v)≤Cv^θ at both v=k⁴ and v=(k+1)⁴ imply G(y)≤(C+225/4)y^θ throughout that interval.
-- source:
--   The prime ramp G and corrected one-sided window formulation are the campaign theorem 4929ef0c (https://prove2.me/theorems/4929ef0c-b2f4-4cfe-a318-614c3a767339), inspired by Alpöge’s one-sided criterion. The secant estimate and the reduction to fourth-power mesh points follow directly from positivity of Λ, convexity of each positive-part ramp, and log u≤u−1.

import Mathlib

set_option autoImplicit false

open Finset ArithmeticFunction
namespace MasulloRH

theorem prime_ramp_chord_and_fourth_power_bound :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    (∀ a b t : ℝ, 0<a → a≤b → 0≤t → t≤1 → let y := (1-t)*a+t*b
      G y ≤ (1-t)*G a+t*G b+t*(1-t)*(b-a)^2/y) ∧
    (∀ k : ℕ, 1≤k → ∀ θ C : ℝ, 1/2≤θ → θ≤1 → 0≤C →
      G ((k:ℝ)^4) ≤ C*((k:ℝ)^4)^θ → G (((k:ℝ)+1)^4) ≤ C*(((k:ℝ)+1)^4)^θ →
      ∀ y : ℝ, (k:ℝ)^4 ≤ y → y ≤ ((k:ℝ)+1)^4 → G y ≤ (C+225/4)*y^θ) := by sorry

end MasulloRH
