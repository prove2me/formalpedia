-- Prove2me | Theorems.Thm_ImpulsiveISS_FixedDwell_dwell_step
-- name    : ImpulsiveISS.FixedDwell.dwell_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:44:59.164332+00:00
-- url     : https://prove2.me/theorems/bb254e11-e4e8-4451-a2bf-74ad9341b923
-- title:
--   Proof of Theorem 1, p. 7, (3.14) — one dwell interval lowers F(V(x)) by δ when u ≡ 0
-- statement:
--   Assume the hypotheses of Theorem 1: an impulsive system with an ISS-Lyapunov function $V$ in max form with flow rate $\varphi\in\mathcal P$, jump rate $\alpha\in\mathcal P$, and $\theta,\delta>0$ satisfying the dwell-time condition (3.7), $\int_a^{\alpha(a)}ds/\varphi(s)\le\theta-\delta$ for all $a>0$. Let $t_1<t_2<\cdots$ be an impulse sequence in $S_\theta$, fix $x_0\in X$ and $r>0$, let $x(\cdot)$ be the trajectory from $x_0$ with zero input $u\equiv0$, and put $y(t)=V(x(t))$ and $F(q)=\int_r^q ds/\varphi(s)$.
--
--   If $y(t)>0$ for all $t\in[t_i,t_{i+1}]$, then
--   $$F(y(t_{i+1}))-F(y(t_i))\le-\delta .$$
--
--   This is the step from (3.13) to (3.14): one dwell interval decreases $F(y)$ along the flow by at least $\theta$, the jump increases it by at most $\theta-\delta$, so the net change is at most $-\delta$. Iterating it gives (3.15).
--
--   **Formalization Note** Impulse times are 0-based: `τ i` is the paper's $t_{i+1}$, so the interval $[t_i,t_{i+1}]$ of the statement is `[τ i, τ (i+1)]`. Positivity is required on the closed interval, including the post-jump value $y(t_{i+1})$, because $F$ is applied to it; the page's (3.14) presupposes the same. With $u\equiv0$ the jump input is $u^-(t_{i+1})=0$ and $\gamma(0)=0$, so (3.6) reads $V(g(x,0))\le\alpha(V(x))$, the page's (3.9).
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 7, proof of Theorem 1, (3.13)–(3.14)

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.FixedDwell

/-- (3.13)–(3.14), p. 7: for zero input and an impulse sequence in `S_θ`, if
`y = V(x(·))` stays positive on `[t_i, t_{i+1}]` (`τ i`, `τ (i+1)` here), then one dwell
interval lowers `F(q) = ∫_r^q ds/φ(s)` by at least `δ`:
`F(y(t_{i+1})) − F(y(t_i)) ≤ −δ`. -/
theorem dwell_step {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : System X U) (hS : IsImpulsiveSystem S)
    (V : X → ℝ≥0) (ψ₁ ψ₂ γ α φ : ℝ≥0 → ℝ≥0) (hV : IsISSLyapunovMax S V ψ₁ ψ₂ γ α φ)
    (hφ : IsPosDef φ) (θ δ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (h37 : DwellCondition α φ θ δ)
    (τ : ℕ → ℝ) (hτ : InSTheta θ τ) (x₀ : X) (r : ℝ) (hr : 0 < r) (i : ℕ)
    (hpos : ∀ t ∈ Set.Icc (τ i) (τ (i + 1)),
      0 < (V (traj S τ x₀ (fun _ => (0 : U)) t) : ℝ)) :
    Fint φ r (V (traj S τ x₀ (fun _ => (0 : U)) (τ (i + 1))))
      - Fint φ r (V (traj S τ x₀ (fun _ => (0 : U)) (τ i))) ≤ -δ := by sorry

end ImpulsiveISS.FixedDwell
