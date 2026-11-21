-- Prove2me | Theorems.Thm_MasulloGRH_bilateral_local_euler_orbit_two_mellin_lines
-- name    : MasulloGRH.bilateral_local_euler_orbit_two_mellin_lines
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:45:45.763107+00:00
-- url     : https://prove2.me/theorems/f5d6bd72-72dd-43f0-9b0f-c2664fe7f73e
-- title:
--   Bilateral prime-power sampling needs both Mellin lines, with a reciprocal dyadic counterexample
-- statement:
--   For a real base $q>1$, a unit complex phase $u$ and two real abscissae $b<0<a$, put $J(d)=(2\pi)^{-1}\int_{\mathbf R}\mathcal M f(d+iy)/(1-u^{-1}q^{d+iy})\,dy$. If $f$ is continuous at positive reals, the defining Mellin integrals converge at $a,b$, and the transform is integrable on both vertical lines, then $\sum_{k\in\mathbf Z}u^k f(q^k)$ converges absolutely with sum $J(b)-J(a)$. There exists a Schwartz–Bruhat test of exponential decay (Masullo's definition) with $\psi(2^k)=1$ for $k=-1$ and zero for all other integers $k$. Its bilateral dyadic sum equals one, while its normalized single right-line integral $J(1)$ for the trivial character equals zero. This isolates the missing term in (B.4.1.20).
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026, Appendix B, Lemma B.4.1.7, (B.4.1.19)–(B.4.1.20) and (B.4.1.34)–(B.4.1.35), pp. 611–614. Two-line correction to the last equality; the Poisson summation equality is independent. Mellin inversion and Fourier-transform normalization from Mathlib. Builds on the mission's earlier isolated-prime test methodology.

import Definitions.Def_MasulloGRH_MellinRpos
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open MasulloGRH Complex MeasureTheory

theorem MasulloGRH.bilateral_local_euler_orbit_two_mellin_lines :
    (∀ (q a b : ℝ), 1 < q → 0 < a → b < 0 → ∀ u : ℂ, ‖u‖ = 1 → ∀ f : ℝ → ℂ,
      MellinConvergent f a → MellinConvergent f b →
      VerticalIntegrable (mellin f) a → VerticalIntegrable (mellin f) b →
      (∀ x : ℝ, 0 < x → ContinuousAt f x) →
      let J := fun d : ℝ => (1 / (2 * Real.pi) : ℝ) •
        ∫ y : ℝ, mellin f (d+y*I) / (1-u⁻¹*(q : ℂ)^((d:ℂ)+y*I))
      HasSum (fun k : ℤ => u^k * f (q^k)) (J b - J a)) ∧
    (∃ ψ : ℝ → ℂ, HasExpDecay ψ ∧
      (∀ k : ℤ, ψ ((2:ℝ)^k) = if k = -1 then 1 else 0) ∧
      (∑' k : ℤ, ψ ((2:ℝ)^k)) = 1 ∧ VerticalIntegrable (mellin ψ) 1 ∧
      ((1 / (2 * Real.pi) : ℝ) • ∫ y : ℝ, mellin ψ (1+y*I) / (1-(2 : ℂ)^(1+(y:ℂ)*I)))=0) := by sorry
