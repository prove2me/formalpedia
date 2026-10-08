-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_lemma_A_1
-- name    : GJNSteadyState.Interchange.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:58.635122+00:00
-- url     : https://prove2.me/theorems/5ef4e165-aa00-47e4-bfc9-84f3c78bec75
-- title:
--   Lemma A.1, p. 25 — uniform moment bounds on sup_{t≤n} ‖Xⁿ(t) − xⁿ_z(t)‖ over all initial states
-- statement:
--   Let $\Xi^n$ be the heavy-traffic sequence built from a critically loaded GJN $\Xi$ and $\kappa^0>0$, let $X^n$ be the net input process (6) of $\Xi^n$ and $x^n_z(t)=z+(\alpha^n-(I-P')\mu)t$ its fluid counterpart started at $z$, and write $\|\cdot\|$ for the $\ell^1$ norm. There is $\theta_1>0$ such that
--   $$\limsup_{n\to\infty}\sup_{(z,a,v)\in\mathcal X}n^{-1/2}\,\mathbb E\Big[\sup_{0\le t\le n}\|X^n(t)-x^n_z(t)\|\ \Big|\ \bar Q^n(0)=(z,a,v)\Big]<\infty, \tag{39}$$
--   $$\limsup_{n\to\infty}\sup_{(z,a,v)\in\mathcal X}\mathbb E\Big[\sup_{0\le t\le n}e^{n^{-1/2}\theta_1\|X^n(t)-x^n_z(t)\|}\ \Big|\ \bar Q^n(0)=(z,a,v)\Big]<\infty, \tag{40}$$
--   $$\limsup_{n\to\infty}\sup_{(z,a,v)\in\mathcal X}n^{-1}\,\mathbb E\Big[\sup_{0\le t\le n}\|X^n(t)-x^n_z(t)\|^2e^{n^{-1/2}\theta_1\|X^n(t)-x^n_z(t)\|}\ \Big|\ \bar Q^n(0)=(z,a,v)\Big]<\infty. \tag{41}$$
--
--   The supremum is over all initial states, including all elapsed interarrival and service times; condition (1)–(2) is what makes the bounds uniform in them. The lemma feeds the proof of Proposition 2.
--
--   **Formalization Note** Each "$\limsup_n\sup_x\ldots<\infty$" is rendered as: there is a finite $C$ such that for all sufficiently large $n$, every initial state $x$ and every realization of $\Xi^n$ from $\delta_x$, the expectation is at most $C$; one $C$ serves all three bounds. The initial state ranges over $\mathcal X=\mathbb Z_+^J\times\mathbb R_+^{2J}$ (`InStateSpace`: nonnegative elapsed times); a negative "elapsed time" would delay the first arrival or service without bound and is not a state of the network. Expectations are lower Lebesgue integrals in $[0,\infty]$ and the suprema over $t\in[0,n]$ are taken inside them. In (41) the supremum is applied to the product, which equals the product of the suprema since $r\mapsto r^2e^{cr}$ is increasing.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 25, Lemma A.1, (39)–(41); net input (6), p. 8

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Lemma A.1 (p. 25): for the net input process `Xⁿ` of `Ξⁿ` and its fluid counterpart
`xⁿ_z(t) = z + (αⁿ − (I − P′)μ) t`, there is `θ₁ > 0` such that, uniformly over initial states
`(z, a, v) ∈ 𝒳 = ℤ₊^J × ℝ₊^{2J}` and for all large `n`, the quantities
`n^{−1/2} E sup_{t ≤ n} ‖Xⁿ(t) − xⁿ_z(t)‖`, `E sup_{t ≤ n} exp(n^{−1/2} θ₁ ‖Xⁿ(t) − xⁿ_z(t)‖)` and
`n^{−1} E sup_{t ≤ n} ‖Xⁿ(t) − xⁿ_z(t)‖² exp(n^{−1/2} θ₁ ‖Xⁿ(t) − xⁿ_z(t)‖)` stay bounded
(`‖·‖` the `ℓ¹` norm). -/
theorem lemma_A_1 {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ C : NNReal, ∀ᶠ n : ℕ in atTop,
      ∀ (x : State J), InStateSpace x → ∀ R : Realization (htNet Ξ κ0 n) (Measure.dirac x),
        let D : ℝ → R.Ω → ℝ := fun t ω =>
          ∑ j, |R.netInput t ω j - fluidInput (htNet Ξ κ0 n) (fun i => (x.1 i : ℝ)) t j|
        ENNReal.ofReal (1 / Real.sqrt n) *
            ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (D t ω) ∂(R.P) ≤ C ∧
          ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) n,
              ENNReal.ofReal (Real.exp (θ₁ / Real.sqrt n * D t ω)) ∂(R.P) ≤ C ∧
          ENNReal.ofReal (1 / (n : ℝ)) *
              ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) n,
                ENNReal.ofReal (D t ω ^ 2 * Real.exp (θ₁ / Real.sqrt n * D t ω)) ∂(R.P) ≤ C := by sorry

end GJNSteadyState.Interchange
