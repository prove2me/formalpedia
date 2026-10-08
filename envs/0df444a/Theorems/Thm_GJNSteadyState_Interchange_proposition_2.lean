-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_proposition_2
-- name    : GJNSteadyState.Interchange.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:38.963822+00:00
-- url     : https://prove2.me/theorems/98627209-4339-4587-b806-9b510cef076a
-- title:
--   Proposition 2, p. 17 — the workload w′Qⁿ drifts down by √n over time nt₀ and has uniform exponential moments
-- statement:
--   Let $\Xi^n$ be the heavy-traffic sequence built from a critically loaded GJN $\Xi$ and $\kappa^0>0$, with queue lengths $Q^n$ and workload vector $w=e'[I-P']^{-1}$. There exist constants $t_0,c_0>0$, depending only on $\Xi$ and not on $n$, such that for all sufficiently large $n$
--   $$\sup_{(z,a,v):\,w'z>c_0\sqrt n}\Big\{\mathbb E\big[w'Q^n(nt_0)\,\big|\,\bar Q^n(0)=(z,a,v)\big]-w'z\Big\}\le-\sqrt n. \tag{30}$$
--   In addition there exists $\theta_0>0$, depending only on $\Xi$, such that
--   $$\limsup_{n\to\infty}\sup_{(z,a,v)\in\mathcal X}\mathbb E\Big[e^{n^{-1/2}\theta_0(w'Q^n(nt_0)-w'z)^+}\,\Big|\,\bar Q^n(0)=(z,a,v)\Big]<\infty \tag{31}$$
--   and
--   $$\limsup_{n\to\infty}\sup_{(z,a,v)\in\mathcal X}n^{-1}\,\mathbb E\Big[(w'Q^n(nt_0)-w'z)^2e^{n^{-1/2}\theta_0(w'Q^n(nt_0)-w'z)^+}\,\Big|\,\bar Q^n(0)=(z,a,v)\Big]<\infty. \tag{32}$$
--
--   This is the drift and moment input that makes the workload a Lyapunov function in Proposition 3.
--
--   **Formalization Note** (30) is written as $\mathbb E[w'Q^n(nt_0)]+\sqrt n\le w'z$ in $[0,\infty]$ for every realization of $\Xi^n$ from $\delta_{(z,a,v)}$ with $w'z>c_0\sqrt n$. Each $\limsup<\infty$ is rendered as one finite $C$ bounding (31) and (32) for all large $n$, uniformly over initial states in $\mathcal X=\mathbb Z_+^J\times\mathbb R_+^{2J}$ (`InStateSpace`: nonnegative elapsed times) and realizations. The constants $t_0,c_0$ are chosen before $n$, and $\theta_0$ after them (on the page $\theta_0$ may depend on $t_0$).
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 17, Proposition 2, (30)–(32)

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Proposition 2 (p. 17): there are `t₀, c₀ > 0`, depending only on `Ξ`, such that for all
large `n`, (30) `E[w′Qⁿ(nt₀) | Q̄ⁿ(0) = (z, a, v)] − w′z ≤ −√n` whenever `w′z > c₀√n`; and there
is `θ₀ > 0` such that (31) `E[exp(n^{−1/2}θ₀(w′Qⁿ(nt₀) − w′z)⁺) | Q̄ⁿ(0) = (z, a, v)]` and (32)
`n^{−1} E[(w′Qⁿ(nt₀) − w′z)² exp(n^{−1/2}θ₀(w′Qⁿ(nt₀) − w′z)⁺) | Q̄ⁿ(0) = (z, a, v)]` are bounded
uniformly over `(z, a, v) ∈ 𝒳 = ℤ₊^J × ℝ₊^{2J}` for all large `n`. -/
theorem proposition_2 {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j) :
    ∃ t₀ c₀ : ℝ, 0 < t₀ ∧ 0 < c₀ ∧
      (∀ᶠ n : ℕ in atTop, ∀ (x : State J), InStateSpace x →
        c₀ * Real.sqrt n < wvec Ξ ⬝ᵥ (fun j => (x.1 j : ℝ)) →
        ∀ R : Realization (htNet Ξ κ0 n) (Measure.dirac x),
          ∫⁻ ω, ENNReal.ofReal (wvec Ξ ⬝ᵥ (fun j => (R.Q (n * t₀) ω j : ℝ))) ∂(R.P)
              + ENNReal.ofReal (Real.sqrt n) ≤
            ENNReal.ofReal (wvec Ξ ⬝ᵥ (fun j => (x.1 j : ℝ)))) ∧
      ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∃ C : NNReal, ∀ᶠ n : ℕ in atTop,
        ∀ (x : State J), InStateSpace x → ∀ R : Realization (htNet Ξ κ0 n) (Measure.dirac x),
          let Δ : R.Ω → ℝ := fun ω =>
            wvec Ξ ⬝ᵥ (fun j => (R.Q (n * t₀) ω j : ℝ)) - wvec Ξ ⬝ᵥ (fun j => (x.1 j : ℝ))
          ∫⁻ ω, ENNReal.ofReal (Real.exp (θ₀ / Real.sqrt n * max (Δ ω) 0)) ∂(R.P) ≤ C ∧
            ENNReal.ofReal (1 / (n : ℝ)) *
                ∫⁻ ω, ENNReal.ofReal (Δ ω ^ 2 * Real.exp (θ₀ / Real.sqrt n * max (Δ ω) 0)) ∂(R.P)
              ≤ C := by sorry

end GJNSteadyState.Interchange
