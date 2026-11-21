-- Prove2me | Theorems.Thm_MasulloRH_finite_padic_valuation_chart_fourier_nonfactorization
-- name    : MasulloRH.finite_padic_valuation_chart_fourier_nonfactorization
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:57:50.681891+00:00
-- url     : https://prove2.me/theorems/fb0b39d4-e652-433a-a178-f3cc9bb400e8
-- title:
--   Finite unit-chart periodization loses Fourier information at every integer cutoff
-- statement:
--   Let $p$ be prime, $\mu$ additive Haar measure on $\mathbf Q_p$, and $\psi$ an additive character trivial on $\mathbf Z_p$. For any nonempty finite $K\subset\mathbf Z$, restrict the finite periodization $A_Kf(s,u)=\sum_{j\in K}f(p^js,p^ju)$ to the unit chart $\|u\|_p=1$. For an input supported on $v_p(y)=\ell$, the full $p^\mathbf Z$ periodization at each $y\ne0$ has only its $\ell-v_p(y)$ summand.
--
--   There is an integer $L$ and a positive-measure annulus $\Omega=\{y:v_p(y)=L\}$ such that $f(x,y)=e^{-\pi x^2}1_\Omega(y)$ has $A_K f=0$ everywhere on the unit chart, while
--   $$A_K\widehat f(s,u)=\mu(\Omega)\sum_{j\in K}e^{-\pi(p^js)^2}>0.$$
--   Here $\widehat f$ is the iterated additive Fourier transform on the two places. The same annulus admits a real-place smooth compactly supported test inside $(1,2)$ with identically zero physical chart stage and strictly positive real part of the Fourier stage at a common positive real frequency for all $p$-adic units. In particular a fixed-stage rule on the physical chart alone cannot recover the Fourier stage.
-- source:
--   Unit-valuation chart for the rational S-unit action in Masullo, The Music of the Primes, Chapters 11–12, especially the S-local quotient and Fourier cutoff in §12.4.1. Uses genuine additive Haar integration on Q_p and the archimedean Gaussian Fourier identity.

import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open MeasureTheory Set Filter
open scoped FourierTransform Topology

theorem MasulloRH.finite_padic_valuation_chart_fourier_nonfactorization (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (ψ : AddChar ℚ_[p] ℂ)
    (hψ : ∀ z : ℚ_[p], ‖z‖ ≤ 1 → ψ z = 1) (K : Finset ℤ) (hK : K.Nonempty) :
    let G (s : ℝ) : ℂ := Real.exp (-(Real.pi*s^2))
    let FT (f : ℝ → ℚ_[p] → ℂ) (s : ℝ) (u : ℚ_[p]) :=
      ∫ y : ℚ_[p], ψ (y*u) * (𝓕 (fun x : ℝ => f x y)) s ∂μ
    let stage (f : ℝ → ℚ_[p] → ℂ) (s : ℝ) (u : ℚ_[p]) :=
      ∑ j ∈ K, f ((p:ℝ)^j*s) ((p:ℚ_[p])^j*u)
    (∀ (ℓ : ℤ) (g : ℝ → ℚ_[p] → ℂ),
      (∀ x y, ‖y‖ ≠ ‖(p:ℚ_[p])^ℓ‖ → g x y = 0) →
      ∀ (s : ℝ) (y : ℚ_[p]), y ≠ 0 → let j := ℓ-y.valuation
      HasSum (fun k : ℤ => g ((p:ℝ)^k*s) ((p:ℚ_[p])^k*y))
        (g ((p:ℝ)^j*s) ((p:ℚ_[p])^j*y))) ∧
    ∃ L : ℤ,
      let Ω := Metric.sphere (0:ℚ_[p]) ‖(p:ℚ_[p])^L‖
      let f (x : ℝ) (y : ℚ_[p]) := Ω.indicator (fun _ => G x) y
      (∀ k ∈ K, k < L ∧ 0 ≤ k+L) ∧ 0 < μ.real Ω ∧
      (∀ s : ℝ, ∀ u : ℚ_[p], ‖u‖=1 →
        HasSum (fun j : ℤ => f ((p:ℝ)^j*s) ((p:ℚ_[p])^j*u)) (G ((p:ℝ)^L*s))) ∧
      (∀ s : ℝ, ∀ u : ℚ_[p], ‖u‖=1 → stage f s u = 0 ∧
        stage (FT f) s u = (μ.real Ω:ℂ) * ∑ j ∈ K, G ((p:ℝ)^j*s) ∧
        0 < (stage (FT f) s u).re) ∧
      (∃ b : ℝ → ℂ, ContDiff ℝ (⊤:ℕ∞) b ∧ HasCompactSupport b ∧
        (∀ x : ℝ, x≤1 ∨ 2≤x → b x=0) ∧
        let h (x : ℝ) (y : ℚ_[p]) := Ω.indicator (fun _ => b x) y
        (∀ t : ℝ, ∀ u : ℚ_[p], ‖u‖=1 → stage h t u=0) ∧
        ∃ s : ℝ, 0<s ∧ ∀ u : ℚ_[p], ‖u‖=1 → 0<(stage (FT h) s u).re) := by sorry
