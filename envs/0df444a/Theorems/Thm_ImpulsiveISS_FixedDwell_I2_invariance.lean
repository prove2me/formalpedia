-- Prove2me | Theorems.Thm_ImpulsiveISS_FixedDwell_I2_invariance
-- name    : ImpulsiveISS.FixedDwell.I2_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:15.841232+00:00
-- url     : https://prove2.me/theorems/16f2ee51-61e5-4e38-ae3a-fdfe663a419b
-- title:
--   Proof of Theorem 1, p. 9 — x(t) ∈ I₂ = {V ≤ α̃(‖u‖)} for all t ≥ t*
-- statement:
--   Assume the hypotheses of Theorem 1: an impulsive system with an ISS-Lyapunov function $V$ in max form with gain $\gamma\in\mathcal K_\infty$, flow rate $\varphi\in\mathcal P$, jump rate $\alpha\in\mathcal P$, and $\theta,\delta>0$ satisfying (3.7). Let $T\in S_\theta$, $x_0\in X$, and let $u\in U_c$ with $\|u(t)\|\le M$ for all $t\ge0$. Put
--   $$\tilde\alpha(M)=\max\Big\{\max_{0\le s\le\gamma(M)}\alpha(s),\ \gamma(M)\Big\},\qquad I_1=\{x:V(x)\le\gamma(M)\},\qquad I_2=\{x:V(x)\le\tilde\alpha(M)\}.$$
--   If the trajectory is in $I_1$ at some time $t_1\ge0$, then it stays in $I_2$ afterwards:
--   $$V(x(t))\le\tilde\alpha(M)\qquad\text{for all }t\ge t_1 .$$
--
--   Together with the zero-input decay before the trajectory first reaches $I_1$, this gives the gain $\gamma$ of the ISS estimate (3.18).
--
--   **Formalization Note** The page fixes $t^*=\inf\{t:x(t)\in I_1\}$ and proves $x(t)\in I_2$ for $t\ge t^*$; the statement here starts from any time at which the trajectory is in $I_1$, which avoids the infimum and contains the page's claim. The page's $\chi$ is the gain $\gamma$ of the max form (Proposition 3.1), and $\|u\|_{U_c}$ is replaced by a bound $M$. The inner maximum is `sSup` of the image of the compact interval $[0,\gamma(M)]$ under the continuous $\alpha$, hence a genuine maximum.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 9, proof of Theorem 1, definition of α̃ and I₂ and the claim x(t) ∈ I₂ for all t ≥ t*

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.FixedDwell

/-- p. 9, `x(t) ∈ I₂` for `t ≥ t*`: under the hypotheses of Theorem 1, take an impulse sequence
in `S_θ` and an admissible input `u` with `‖u(t)‖ ≤ M` for `t ≥ 0`. If the trajectory is in
`I₁ = {V ≤ γ(M)}` at some time `t₁ ≥ 0`, then it stays in `I₂ = {V ≤ α̃(M)}` for all
`t ≥ t₁`, where `α̃(M) = max{max_{0≤s≤γ(M)} α(s), γ(M)}`. -/
theorem I2_invariance {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : System X U) (hS : IsImpulsiveSystem S)
    (V : X → ℝ≥0) (ψ₁ ψ₂ γ α φ : ℝ≥0 → ℝ≥0) (hV : IsISSLyapunovMax S V ψ₁ ψ₂ γ α φ)
    (hφ : IsPosDef φ) (θ δ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (h37 : DwellCondition α φ θ δ)
    (τ : ℕ → ℝ) (hτ : InSTheta θ τ) (x₀ : X) (u : ℝ → U) (hu : IsPCInput u) (M : ℝ≥0)
    (hM : ∀ t : ℝ, 0 ≤ t → ‖u t‖₊ ≤ M) (t₁ : ℝ) (ht₁ : 0 ≤ t₁)
    (hin : V (traj S τ x₀ u t₁) ≤ γ M) :
    ∀ t : ℝ, t₁ ≤ t → V (traj S τ x₀ u t) ≤ alphaTilde α γ M := by sorry

end ImpulsiveISS.FixedDwell
