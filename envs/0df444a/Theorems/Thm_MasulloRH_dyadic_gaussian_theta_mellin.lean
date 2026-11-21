-- Prove2me | Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
-- name    : MasulloRH.dyadic_gaussian_theta_mellin
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:00:41.67074+00:00
-- url     : https://prove2.me/theorems/714a2f7b-e260-4499-9c88-2074add3de2b
-- title:
--   An admissible dyadic Gaussian theta test detects the zeta zeros with their orders
-- statement:
--   Write $G(x)=e^{-\pi x^2}$ and $g(x)=G(x)-3G(2x)+2G(4x)$. The function $g$ is Schwartz, $g(0)=0$, and its integral over the real line is zero. For $x>0$ put $\Theta_g(x)=\sum_{n\in\mathbb Z}g(nx)$. Its Mellin integral converges at every $s$ with $0<\Re s<1$, and
--   $$
--   \mathcal M\Theta_g(s)=(1-2^{-s})(1-2^{1-s})\Lambda(s),
--   $$
--   where $\Lambda$ is the completed Riemann zeta function. In this strip the Mellin transform and $\zeta$ have exactly the same zeros and analytic orders. At every real frequency $\nu$, the real-analytic order of the restriction $t\mapsto\mathcal M\Theta_g(1/2-2\pi i t)$ at $\nu$ equals the complex order of $\zeta$ at $1/2-2\pi i\nu$.
--
--   This gives one explicit admissible test whose theta image detects the local jet orders needed in the rational critical-line construction.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, preprint pp. 63–67, equations (14)–(30), https://arxiv.org/abs/math/9811068; A. M. Masullo, The Music of the Primes, §10.2.1.1, pp. 441–443. The particular three-dilate Gaussian is an independently formulated rational test for the theta-image argument. See Calvin Yost-Wolff, Prove2Me discussion d8680fb7-dd35-4a9c-ab4e-5888ec240d48, for the Gaussian-generator strategy.

import Mathlib
open MeasureTheory
open scoped SchwartzMap

theorem MasulloRH.dyadic_gaussian_theta_mellin :
    ∃ g : 𝓢(ℝ,ℂ),
      (∀ x : ℝ, g x = ((Real.exp (-Real.pi*x^2) - 3*Real.exp (-Real.pi*(2*x)^2)
        + 2*Real.exp (-Real.pi*(4*x)^2) : ℝ) : ℂ)) ∧
      g 0 = 0 ∧ (∫ x : ℝ, g x) = 0 ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 →
        HasMellin (fun x : ℝ => ∑' n : ℤ, g ((n:ℝ)*x)) s
          ((1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s) ∧
        (mellin (fun x : ℝ => ∑' n : ℤ, g ((n:ℝ)*x)) s = 0 ↔ riemannZeta s = 0) ∧
        analyticOrderAt (mellin (fun x : ℝ => ∑' n : ℤ, g ((n:ℝ)*x))) s = analyticOrderAt riemannZeta s) ∧
      ∀ ν : ℝ, let σ (x : ℝ) : ℂ := 1/2+((-2*Real.pi : ℝ):ℂ)*Complex.I*(x:ℂ)
        analyticOrderAt (fun x : ℝ => mellin (fun y : ℝ => ∑' n : ℤ, g ((n:ℝ)*y)) (σ x)) ν =
          analyticOrderAt riemannZeta (σ ν) := by sorry
