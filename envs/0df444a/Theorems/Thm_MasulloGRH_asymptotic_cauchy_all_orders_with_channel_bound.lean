-- Prove2me | Theorems.Thm_MasulloGRH_asymptotic_cauchy_all_orders_with_channel_bound
-- name    : MasulloGRH.asymptotic_cauchy_all_orders_with_channel_bound
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:51:34.61401+00:00
-- url     : https://prove2.me/theorems/f6d9482e-2dde-4e7a-b7ca-5a8ae372fbb5
-- title:
--   All-order asymptotic Cauchy formula on strips and half-planes with bounded low-height channels
-- statement:
--   Suppose $\Phi$ is holomorphic on $a<\Re s<b$ with the uniform Schwartz decay at large height of Masullo's Definition B.2.2.1. Let $l=a+\varepsilon<r=b-\varepsilon$, $\varepsilon>0$, and let $V_d(g)=i\int_{\mathbb R} g(d+it)\,dt$. For each integer $N\ge0$, put $g_z(s)=\Phi(s)/(s-z)^{N+1}$. If $z$ lies off both lines, the two integrals converge absolutely and
--   $$\frac{N!}{2\pi i}\big(V_r(g_z)-V_l(g_z)\big)=
--   \begin{cases}\Phi^{(N)}(z)& l<\Re z<r,\\0&\Re z\notin[l,r].\end{cases}$$
--   For the left half-plane $\Re s<b$, assume its source large-height Schwartz condition. Fix $d<b$ and suppose for each $Y>0$ the function is bounded on $\{s:\Re s\le d,\ |\Im s|\le Y\}$. Then $N!\,V_d(g_z)/(2\pi i)$ is absolutely convergent and is $\Phi^{(N)}(z)$ for $\Re z<d$ and zero for $\Re z>d$. These are the finite-strip and half-plane formulas of B.2.2.4 at every derivative order, with a low-height condition for the half-plane.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026, pp. 601–602, Theorem B.2.2.4. Higher derivative extension of the verified value formula 02f88f07-f27e-474c-b3ec-b6473d4460af. This gives the full two-part Cauchy formula, including recovery of the derivatives and the exterior vanishing.

import Definitions.Def_MasulloGRH_MellinRpos
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Complex

theorem MasulloGRH.asymptotic_cauchy_all_orders_with_channel_bound :
(∀ (a b ε : ℝ) (Φ : ℂ → ℂ), 0 < ε → a+ε < b-ε →
      DifferentiableOn ℂ Φ (MasulloGRH.openStrip a b) →
      MasulloGRH.UniformlySchwartzOnStrip Φ a b → ∀ (N : ℕ) (z : ℂ), z.re ≠ a+ε → z.re ≠ b-ε →
      let g := fun s : ℂ => Φ s/(s-z)^(N+1)
      MasulloGRH.VerticalLineIntegrable g (a+ε) ∧ MasulloGRH.VerticalLineIntegrable g (b-ε) ∧
      ((N.factorial:ℂ)/(2*Real.pi*I))*(MasulloGRH.verticalLineIntegral g (b-ε) -
        MasulloGRH.verticalLineIntegral g (a+ε)) =
        if a+ε < z.re ∧ z.re < b-ε then iteratedDeriv N Φ z else 0) ∧
    (∀ (b d : ℝ) (Φ : ℂ → ℂ), d < b → DifferentiableOn ℂ Φ {s : ℂ | s.re < b} →
      MasulloGRH.SchwartzOnLeftHalfPlane Φ b →
      (∀ Y : ℝ, ∃ M : ℝ, ∀ s : ℂ, s.re ≤ d → |s.im| ≤ Y → ‖Φ s‖ ≤ M) →
      ∀ (N : ℕ) (z : ℂ), z.re ≠ d → let g := fun s : ℂ => Φ s/(s-z)^(N+1)
        MasulloGRH.VerticalLineIntegrable g d ∧
          ((N.factorial:ℂ)/(2*Real.pi*I))*MasulloGRH.verticalLineIntegral g d =
            if z.re < d then iteratedDeriv N Φ z else 0) := by sorry
