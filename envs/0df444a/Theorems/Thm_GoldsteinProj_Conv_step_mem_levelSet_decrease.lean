-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_step_mem_levelSet_decrease
-- name    : GoldsteinProj.Conv.step_mem_levelSet_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:23:55.360688+00:00
-- url     : https://prove2.me/theorems/2071b438-e97a-40bc-adf0-d1e9fa861325
-- title:
--   Proof of (i), p. 710 — for σ ≦ ρ ≦ 2ρ₀ − σ: x(ρ) ∈ S and Δ(ρ) ≧ ‖x(ρ) − x_k‖²σ/4ρ₀², with Δ(ρ) > 0 off stationary points
-- statement:
--   Let $H$ be a real Hilbert space, $C \subseteq H$ closed and convex, $P$ the projection onto $C$, and $f : H \to \mathbb R$ continuous on $C$. Let $x_0 \in C$, $S = \{x \in C : f(x) \le f(x_0)\}$, and let $\hat S$ be an open set containing the convex hull of $S$. Assume that for some $\rho_0 > 0$, at every $x \in \hat S$, $f$ is Fréchet differentiable, the directional second derivative $f''(x, h, h)$ exists in the sense of Gâteaux for every $h$, and $|f''(x, h, h)| \le \|h\|^2/\rho_0$. Let $0 < \sigma \le \rho_0$.
--
--   Then for every $y \in S$ and every step $\rho$ with $\sigma \le \rho \le 2\rho_0 - \sigma$, the point $x(\rho) = P(y - \rho \nabla f(y))$ satisfies
--   1. $x(\rho) \in S$;
--   2. $$f(y) - f(x(\rho)) \;\ge\; \frac{\sigma}{4\rho_0^2}\,\|x(\rho) - y\|^2;$$
--   3. if $y$ is not stationary, $f(y) - f(x(\rho)) > 0$.
--
--   Applied with $y = x_k$ and $\rho = \rho_k$, this is the single step of the method; it proves part (i) of the THEOREM.
--
--   **Formalization Note** Continuity of $f$ on $C$ is an addition to the paper's hypotheses. Without it the claim is false: on $H = C = \mathbb R$ with $P$ the identity, $f(x) = (x - 2)^2$ for $x < 1$ and $f(x) = 100$ for $x \ge 1$, $x_0 = 0$, $\hat S = (-1, 1)$, $\rho_0 = 1/2$, $\sigma = 1/4$, the step $\rho = 1/2$ gives $x(\rho) = 2$ with $f(2) = 100 > f(0)$. The paper's hypotheses constrain $f$ only on $\hat S$, which need not contain the closure of $S$.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 710, PROOF, proof of (i), sentences 5–8

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, p. 710, proof of (i): for `y ∈ S` and any step `σ ≤ r ≤ 2ρ₀ - σ`, the point
`x(r) = P(y - r∇f(y))` lies in `S`, `f(y) - f(x(r)) ≥ ‖x(r) - y‖² σ / (4ρ₀²)`, and the decrease is
strictly positive when `y` is not stationary. -/
theorem step_mem_levelSet_decrease {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) :
    ∀ y ∈ levelSet f C x0, ∀ r : ℝ, σ ≤ r → r ≤ 2 * ρ0 - σ →
      P (y - r • gradient f y) ∈ levelSet f C x0 ∧
      σ / (4 * ρ0 ^ 2) * ‖P (y - r • gradient f y) - y‖ ^ 2 ≤ f y - f (P (y - r • gradient f y)) ∧
      (¬ IsStationary f C P y → 0 < f y - f (P (y - r • gradient f y))) := by sorry

end GoldsteinProj.Conv
