-- Prove2me | Theorems.Thm_MasulloRH_smoothed_prime_ramp_upper_windows
-- name    : MasulloRH.smoothed_prime_ramp_upper_windows
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T02:13:34.420047+00:00
-- url     : https://prove2.me/theorems/4929ef0c-b2f4-4cfe-a318-614c3a767339
-- title:
--   One-sided windows for the corrected zeta prime ramp
-- statement:
--   Let $\Lambda$ be von Mangoldt's function, let $\gamma$ be Euler's constant and write $(v)_+=\max(v,0)$. For real $y\ge1$ put
--   $$G(y)=\sum_{1\le n\le y}\Lambda(n)(y/n-1)_+-y(\log y-1-\gamma).$$
--   For each $1/2<\theta<1$, this open obligation asks for constants $\delta>0$ and $C\ge0$ such that arbitrarily large starts $Y$ satisfy
--   $$G(y)\le C y^\theta\qquad(Y\le y\le Y^{1+\delta}).$$
--   The same constants work for every selected interval. This is the zeta specialization of the one-sided prime-ramp estimate used with Alpöge's analytic zero-free criterion. The theorem isolates the arithmetic input for a separate reduction to the mission's right-half-plane nonvanishing statement.
-- source:
--   Levent Alpöge, Lean release accompanying Remark on the Riemann Hypothesis, 20 November 2026, https://alpo.ge/remark.pdf. In the source tree see Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean (Deduction.G) and LandauTheorems/ZeroFreeOfRpowWindow.lean. New rational mission subproblem for https://prove2.me/theorems/12360d46-f4ac-4dcc-93d2-06be16c15a38.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem MasulloRH.smoothed_prime_ramp_upper_windows :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
        (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
          ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0) -
          y * (Real.log y - 1 - Real.eulerMascheroniConstant) ≤ C * y ^ θ := by sorry
