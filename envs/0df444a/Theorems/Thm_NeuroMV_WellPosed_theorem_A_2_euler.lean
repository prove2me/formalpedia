-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_theorem_A_2_euler
-- name    : NeuroMV.WellPosed.theorem_A_2_euler
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:49:18.827151+00:00
-- url     : https://prove2.me/theorems/ee92bbd9-29ab-4144-8a15-a4742a9abf77
-- title:
--   Theorem A.2, p. 23 — the Euler approximation (21) converges to the solution of (20) locally uniformly in probability
-- statement:
--   Under the assumptions of Theorem A.2 (Hypothesis A.1 and the standing assumptions of Appendix A), let $X^{\omega'}$ be the strong solution of (20) and $X^{n,\omega'}$, $n \ge 1$, the Euler approximation (21) with step $\tau/n$, for every $\omega'$. Then for every $T > 0$ and $\mathbb P'$-almost every $\omega'\in\Omega'$,
--
--   $$\lim_{n\to\infty}\mathbb P\Big\{\sup_{t\in[0,T]}\big|X^{n,\omega'}_t - X^{\omega'}_t\big| > \varepsilon\Big\} = 0\qquad\forall\,\varepsilon>0.$$
--
--   This is the convergence half of Theorem A.2: the Euler method of (21) is how the paper constructs solutions of (20).
--
--   **Formalization Note.** The supremum is taken in $[0,\infty]$. The approximation is any process satisfying the integral form of (21) on every step; the solution is any strong solution (they are unique by Theorem A.2).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Theorem A.2, p. 23, with (21), p. 22

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_DelaySDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem theorem_A_2_euler
    {d m : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : NoiseA d m U Ω Ω') (hN : IsNoiseA τ ν Nz)
    (A : CoeffsA d m Ω U Ω') (hA : A.Regular Nz.𝓕)
    (lam : Measure ℝ) (K : ℝ≥0 → Ω' → ℝ) (L Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : HypA1 A ν τ lam K L Kt) (prob' : Measure Ω') [IsProbabilityMeasure prob']
    (X : Ω' → ℝ → Ω → SDEState d) (hX : ∀ ω' : Ω', IsStrongSol20 A ν Nz τ ω' (X ω'))
    (Xn : ℕ → Ω' → ℝ → Ω → SDEState d)
    (hXn : ∀ ns : ℕ, 0 < ns → ∀ ω' : Ω', IsEuler21 A ν Nz τ ω' ns (Xn ns ω')) :
    ∀ T : ℝ, 0 < T → ∀ᵐ ω' ∂prob', ∀ ε : ℝ, 0 < ε →
      Tendsto (fun ns : ℕ => Nz.prob {ω | ENNReal.ofReal ε <
          ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Xn ns ω' t ω - X ω' t ω‖ₑ}) atTop (𝓝 0) := by sorry

end NeuroMV.WellPosed
