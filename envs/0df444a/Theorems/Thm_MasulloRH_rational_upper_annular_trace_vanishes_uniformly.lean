-- Prove2me | Theorems.Thm_MasulloRH_rational_upper_annular_trace_vanishes_uniformly
-- name    : MasulloRH.rational_upper_annular_trace_vanishes_uniformly
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:05:41.746317+00:00
-- url     : https://prove2.me/theorems/65301a42-7e6d-434b-99ad-723ab429f53a
-- title:
--   Uniform decay of the rational two-place annular trace sum with zero total Fourier mass
-- statement:
--   Let $p$ be a prime. Take a Schwartz function $f$ on $\mathbb R$ and a bounded, measurable, compactly supported test $g$ on $\mathbb Q_p$ which is invariant under translation by a fixed ball around zero. Assume additive translation invariance and a linear upper bound for the volume of every centered $p$-adic ball. The measurable additive character $\psi$ has modulus at most one and $\psi(p^{-1})\ne1$.
--   For each signed rational $S$-unit $\xi=\pm p^k$, twist $f(x)g(y)$ by $e^{2\pi i\xi x}\psi(\xi y)$ and let $m_\xi$ be its full integral. Let $J_\xi(b,T)$ be the twisted integral with logarithmic weight $\max\{T-\max\{\log|x|+\log\|y\|_p,b\},0\}$. If the family $(m_\xi)$ has sum zero, there exists a constant $C$ such that for all real $b\le T$ the family $(J_\xi(b,T))$ is summable and
--   $$\left|\sum_{\xi=\pm p^k} J_\xi(b,T)\right|\le C e^{-b}.$$
--   In particular the sum tends to zero uniformly over $T\ge b$ as $b\to+\infty$.
-- source:
--   New scalar Fourier estimate for the rational two-place specialization of Masullo, The Music of the Primes, Chapter 12, §12.4.1, footnote 2 on p. 514 and equations (12.4.1.22–24) on pp. 517–518. The statement concerns the scalar annular orbital integral, conditional on zero total Fourier mass. Frozen manuscript: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=517

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Trigonometric

open MeasureTheory Filter
open scoped SchwartzMap Padic ENNReal Topology

theorem MasulloRH.rational_upper_annular_trace_vanishes_uniformly (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
    (μ : Measure ℚ_[p]) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψm : Measurable ψ) (hψ : ψ ((p:ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1)
    (f : 𝓢(ℝ,ℂ)) (g : ℚ_[p] → ℂ) (hgm : Measurable g)
    (V M S L : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M) (hS : 0 < S) (hL : 0 < L)
    (hμ : ∀ u : ℝ, 0 < u → μ (Metric.ball 0 u) ≤ ENNReal.ofReal (V*u))
    (hgB : ∀ y, ‖g y‖ ≤ M) (hgS : ∀ y, S ≤ ‖y‖ → g y = 0)
    (hgP : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y) :
    let v (z : ℝ × ℚ_[p]) := Real.log ‖z.1‖ + Real.log ‖z.2‖
    let F (i : Bool × ℤ) (x : ℝ) := f x * Complex.exp
      (((2*Real.pi*((if i.1 then -1 else 1)*(p:ℝ)^i.2):ℝ):ℂ)*Complex.I*(x:ℂ))
    let G (i : Bool × ℤ) (y : ℚ_[p]) := g y * ψ (((if i.1 then -1 else 1)*(p:ℚ_[p])^i.2)*y)
    let mass (i : Bool × ℤ) := (∫ x, F i x)*(∫ y, G i y ∂μ)
    let J (i : Bool × ℤ) (b T : ℝ) := ∫ z : ℝ × ℚ_[p],
      max (T - max (v z) b) 0 • (F i z.1 * G i z.2) ∂(volume.prod μ)
    HasSum mass 0 → ∃ C : ℝ, 0 ≤ C ∧
      (∀ b T : ℝ, b ≤ T → Summable (fun i ↦ J i b T) ∧ ‖∑' i, J i b T‖ ≤ C*Real.exp (-b)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℝ in atTop, ∀ T : ℝ, b ≤ T → ‖∑' i, J i b T‖ < ε := by sorry
