-- Prove2me | Theorems.Thm_MasulloGRH_asymptotic_cauchy_value_formula_with_channel_bound
-- name    : MasulloGRH.asymptotic_cauchy_value_formula_with_channel_bound
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:45:29.678057+00:00
-- url     : https://prove2.me/theorems/02f88f07-f27e-474c-b3ec-b6473d4460af
-- title:
--   Asymptotic Cauchy value formula on strips and on half-planes with bounded low-height channels
-- statement:
--   Let $\Phi$ be holomorphic on $a<\Re s<b$ and uniformly Schwartz in height on each narrower closed strip in the sense of Masullo B.2.2.1. Write $V_c(g)=i\int_{\mathbb R}g(c+it)\,dt$ and $g_z(s)=\Phi(s)/(s-z)$. For $l=a+\varepsilon<r=b-\varepsilon$ with $\varepsilon>0$, the vertical integrals on both lines are absolutely convergent for every $z$ off those two lines. Then $(V_r(g_z)-V_l(g_z))/(2\pi i)$ equals $\Phi(z)$ when $l<\Re z<r$ and zero when $z$ lies outside the closed strip. If $\Phi$ is holomorphic and uniformly Schwartz at large heights on $\Re s<b$ in the source's half-plane sense, fix $d<b$. Assume in addition that for each $Y$ the values $|\Phi(s)|$ are uniformly bounded over $\Re s\le d$ and $|\Im s|\le Y$. Then $V_d(g_z)$ converges absolutely off its line and $V_d(g_z)/(2\pi i)$ equals $\Phi(z)$ for $\Re z<d$ and zero for $\Re z>d$. This is the value case $N=0$ of B.2.2.4 with one additional half-plane hypothesis.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026, Definition B.2.2.1 and Theorem B.2.2.4, pp. 601–602. Corrected value case of finite-strip and left half-plane formulas. Uses the proved Prove2Me rectangle residue theorem 299e7a8f-01fb-4658-8333-905ab08a5fde (PrimeNumberTheoremAnd).

import Definitions.Def_MasulloGRH_MellinRpos

open Complex

theorem MasulloGRH.asymptotic_cauchy_value_formula_with_channel_bound :
    (∀ (a b ε : ℝ) (F : ℂ → ℂ), 0 < ε → a+ε < b-ε →
      DifferentiableOn ℂ F (MasulloGRH.openStrip a b) →
      MasulloGRH.UniformlySchwartzOnStrip F a b → ∀ z : ℂ, z.re ≠ a+ε → z.re ≠ b-ε →
      let g := fun s : ℂ => F s/(s-z)
      MasulloGRH.VerticalLineIntegrable g (a+ε) ∧ MasulloGRH.VerticalLineIntegrable g (b-ε) ∧
      (1/(2*Real.pi*I))*(MasulloGRH.verticalLineIntegral g (b-ε) - MasulloGRH.verticalLineIntegral g (a+ε)) =
        if a+ε < z.re ∧ z.re < b-ε then F z else 0) ∧
    (∀ (b d : ℝ) (F : ℂ → ℂ), d < b → DifferentiableOn ℂ F {s : ℂ | s.re < b} →
      MasulloGRH.SchwartzOnLeftHalfPlane F b →
      (∀ Y : ℝ, ∃ M : ℝ, ∀ s : ℂ, s.re ≤ d → |s.im| ≤ Y → ‖F s‖ ≤ M) →
      ∀ z : ℂ, z.re ≠ d → let g := fun s : ℂ => F s/(s-z)
        MasulloGRH.VerticalLineIntegrable g d ∧
          (1/(2*Real.pi*I))*MasulloGRH.verticalLineIntegral g d = if z.re < d then F z else 0) := by sorry
