-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_proposition_1
-- name    : GJNSteadyState.Interchange.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:07.411568+00:00
-- url     : https://prove2.me/theorems/9ec087c1-652e-40c9-baa3-3b6349095ece
-- title:
--   Proposition 1, p. 11 — fluid stability of the GJN: w′q drains at rate min_j μ_j(1 − ρ_j)
-- statement:
--   Let $\Xi$ be a generalized Jackson network with arrival rates $\alpha$, service rates $\mu$, routing matrix $P$ and traffic intensities $\rho$, and let $w=e'[I-P']^{-1}$. For $z\in\mathbb R^J_+$ let $x_z(t) = z+(\alpha-(I-P')\mu)t$ and let $(y,q)$ solve the Skorohod problem $q(t)=x_z(t)+[I-P']y(t)\ge0$, $y(0)=0$, $y$ nondecreasing and increasing only when $q_j=0$ (the **fluid model**). Then
--
--   1. $q$ is differentiable at almost every $t>0$;
--   2. if $\rho_j\le1$ for every $j$, then $w'\dot q(t)\le-\min_{1\le j\le J}\mu_j(1-\rho_j)$ whenever $q(t)\ne0$ and $q$ is differentiable at $t$;
--   3. if $\rho^*=\max_j\rho_j<1$, there is
--   $$0\le\tau\le\frac{w'z}{\min_{1\le j\le J}\mu_j(1-\rho_j)} \tag{16}$$
--   such that $q(t)=0$ for all $t\ge\tau$.
--
--   The workload $w'q$ is thus a Lyapunov function for the fluid model; its stochastic counterpart is Proposition 2.
--
--   **Formalization Note** Differentiability at $t>0$ is two-sided. The reflection pair is the published `IsReflectionPair` in row form $q=x+y(I-P)$, coordinatewise the page's $q=x+[I-P']y$. The minimum over stations is an infimum over `Fin J`. The statement is for every reflection pair of $x_z$ (Theorem 1 says it is unique). $\tau\ge0$ is implicit on the page. The page states the derivative bound of item 2 with no condition on $\rho$. It is false when two stations are overloaded: with $P=0$, $\alpha=(2,2)$, $\mu=(1,1)$ and $z=(1,1)$, the fluid path is $q(t)=z+t(1,1)$ and $w'\dot q=2>1=-\min_j\mu_j(1-\rho_j)$. It is therefore stated under $\rho_j\le1$ for all $j$, which covers every use in the paper ($\rho^*<1$ in item 3, $\rho^n<1$ in (43)).
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 11, Proposition 1, (15)–(16) (cited from Chen–Yao, Fundamentals of Queueing Networks, Ch. 7)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_GJNSteadyState_Interchange_Network
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Proposition 1 (p. 11, fluid stability of the GJN): for `z ∈ ℝ₊^J` let `(y, q)` solve the
Skorohod problem for the fluid input `x_z(t) = z + (α − (I − P′)μ) t`. Then `q` is
differentiable at almost every `t > 0`; if `ρ_j ≤ 1` for every `j`, then
`w′q̇(t) ≤ −min_j μ_j(1 − ρ_j)` wherever `q(t) ≠ 0` and `q` is differentiable at `t`; and if
`ρ* < 1`, there is `τ ≤ w′z / min_j μ_j(1 − ρ_j)` with `q(t) = 0` for all `t ≥ τ`. The page states
the derivative bound without a condition on `ρ`; it fails when two stations are overloaded
(`P = 0`, `α = (2, 2)`, `μ = (1, 1)`, `q(t) = z + t(1, 1)`: `w′q̇ = 2 > 1`), so it is stated
under `ρ ≤ 1`, which covers every use in the paper (`ρ* < 1` here, `ρⁿ < 1` in (43)). -/
theorem proposition_1 {J : ℕ} (N : Network J) (hN : N.IsGJN) (z : Fin J → ℝ) (hz : 0 ≤ z)
    (y q : ℝ → Fin J → ℝ)
    (hyq : Reiman84.QueueLength.IsReflectionPair N.P
      (fun t => z + t • (alpha N - (1 - N.Pᵀ) *ᵥ mu N)) y q) :
    (∀ᵐ t ∂(volume : Measure ℝ), 0 < t → DifferentiableAt ℝ q t) ∧
    ((∀ j, rho N j ≤ 1) → ∀ t : ℝ, 0 < t → q t ≠ 0 → DifferentiableAt ℝ q t →
      wvec N ⬝ᵥ deriv q t ≤ -(⨅ j, mu N j * (1 - rho N j))) ∧
    ((∀ j, rho N j < 1) →
      ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ (wvec N ⬝ᵥ z) / (⨅ j, mu N j * (1 - rho N j)) ∧
        ∀ t : ℝ, τ ≤ t → q t = 0) := by sorry

end GJNSteadyState.Interchange
