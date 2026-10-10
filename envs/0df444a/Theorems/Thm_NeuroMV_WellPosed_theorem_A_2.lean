-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_theorem_A_2
-- name    : NeuroMV.WellPosed.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:49:04.44199+00:00
-- url     : https://prove2.me/theorems/15204e68-049d-4072-8245-f251a2bc9482
-- title:
--   Theorem A.2, p. 23 — (20) has a unique strong solution, measurable in (t, ω, ω′), with the moment bound (22)
-- statement:
--   Consider the stochastic delay equation (20) with progressively measurable, path-dependent coefficients $f,g$, a predictable jump coefficient $h$, and an initial condition $z^{\omega'}$ as in the definition module, and assume Hypothesis A.1 with rates $K$, $L(R)$, $\tilde K(R)$.
--
--   Then there is a process $X^{\omega'}_t(\omega)$, jointly measurable in $(t,\omega,\omega') \in [-\tau,\infty)\times\Omega\times\Omega'$, such that for every $\omega'$:
--   1. $X^{\omega'}$ is a strong solution of (20);
--   2. it is unique: every strong solution $Y$ of (20) satisfies $\mathbb P\{X^{\omega'}_s = Y_s\} = 1$ for every $s \ge 0$;
--   3. for every $t \ge 0$,
--
--   $$1 + 2\,\mathbb E|X^{\omega'}_t|^2 \le \Big(1 + 2\sup_{u\in[-\tau,0]}\mathbb E|z^{\omega'}_u|^2\Big)\exp\Big(\int_0^t 2K_s(\omega')\,ds\Big). \tag{22}$$
--
--   This is the tool used in §2 to construct each step of the Euler scheme (11) for the McKean–Vlasov equation (6), and it is used for the network (1) as well.
--
--   **Formalization Note.** Expectations are lower Lebesgue integrals in $[0,\infty]$. The convergence of the Euler approximation (21), the other half of Theorem A.2, is the separate item `theorem_A_2_euler`.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Theorem A.2 and (22), p. 23, with (20) and Hypothesis A.1, p. 22; uniqueness as proved on p. 30

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_DelaySDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem theorem_A_2
    {d m : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : NoiseA d m U Ω Ω') (hN : IsNoiseA τ ν Nz)
    (A : CoeffsA d m Ω U Ω') (hA : A.Regular Nz.𝓕)
    (lam : Measure ℝ) (K : ℝ≥0 → Ω' → ℝ) (L Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : HypA1 A ν τ lam K L Kt) :
    ∃ X : Ω' → ℝ → Ω → SDEState d,
      Measurable (fun p : Set.Ici (-τ) × Ω × Ω' => X p.2.2 p.1 p.2.1) ∧
      ∀ ω' : Ω', IsStrongSol20 A ν Nz τ ω' (X ω') ∧
        (∀ Y : ℝ → Ω → SDEState d, IsStrongSol20 A ν Nz τ ω' Y →
          ∀ s : ℝ≥0, ∀ᵐ ω ∂Nz.prob, X ω' s ω = Y s ω) ∧
        ∀ t : ℝ≥0, 1 + 2 * ∫⁻ ω, ‖X ω' t ω‖ₑ ^ 2 ∂Nz.prob ≤
          (1 + 2 * ⨆ u ∈ Set.Icc (-τ) 0, ∫⁻ ω, ‖Nz.z ω' u ω‖ₑ ^ 2 ∂Nz.prob) *
            ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..(t : ℝ), 2 * K s.toNNReal ω')) := by sorry

end NeuroMV.WellPosed
