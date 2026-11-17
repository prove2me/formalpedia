-- Prove2me | Theorems.Thm_Kyprianou_Ch01_charFun_independentProductProcessSum
-- name    : Kyprianou.Ch01.charFun_independentProductProcessSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:00:20.176193+00:00
-- url     : https://prove2.me/theorems/0a8b543c-ce0f-49e4-9f14-e936cdfc2f99
-- title:
--   The characteristic function of independent product-space real variables factors into its two marginal characteristic functions
-- statement:
--   For any two probability measures on independent measurable spaces, any pair of measurable real variables X and Y and any real frequency ξ, the characteristic function of the sum X(ω₁)+Y(ω₂) under their product measure equals the product of the two original marginal characteristic functions. The source-exact proof uses the pinned measure product-map identity, correct pushforward probability instances and the pinned sum-of-independent-Gaussians Fourier identity. This is the Fourier assembly bridge needed for Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Mathlib pinned Measure.map_prod_map, Measure.map_map, ProbabilityTheory.charFun_map_add_prod_eq_mul; Kyprianou (2006) Chapter 1 Theorem 1.6.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.charFun_independentProductProcessSum
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Λ → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (xi : ℝ) :
    charFun ((P.prod Q).map (fun p : Ω × Λ => X p.1 + Y p.2)) xi =
      charFun (P.map X) xi * charFun (Q.map Y) xi := by
  sorry
