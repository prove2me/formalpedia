-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_taylor_estimate
-- name    : GoldsteinProj.Conv.taylor_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:01.497988+00:00
-- url     : https://prove2.me/theorems/845d5fcd-a46b-40ef-b58d-ab51d619ef01
-- title:
--   Proof of (i), p. 710 — Taylor estimate Δ(ρ) ≧ ‖δ(ρ)‖²/ρ − f″(ξ(ρ), δ(ρ), δ(ρ))/2 with ξ(ρ) = x_k + tδ(ρ), t ∈ (0, 1)
-- statement:
--   Let $H$ be a real Hilbert space with inner product $[\cdot,\cdot]$, $C \subseteq H$ convex, $P$ the projection onto $C$, and $f : H \to \mathbb R$. Assume, on a set $\hat S$ and for some $\rho_0 > 0$, that $f$ is Fréchet differentiable at every $x \in \hat S$, that the directional second derivative $f''(x, h, h)$ exists in the sense of Gâteaux for all $h$, and $|f''(x, h, h)| \le \|h\|^2 / \rho_0$.
--
--   Let $y \in C$, $\rho > 0$, and set
--   $$x(\rho) = P(y - \rho \nabla f(y)), \qquad \delta(\rho) = x(\rho) - y, \qquad \Delta(\rho) = f(y) - f(x(\rho)).$$
--   If the segment $[y, x(\rho)]$ lies in $\hat S$, then there is $t \in (0, 1)$ such that, with $\xi = y + t\,\delta(\rho)$,
--   $$\Delta(\rho) \;\ge\; \frac{\|\delta(\rho)\|^2}{\rho} - \frac{f''(\xi, \delta(\rho), \delta(\rho))}{2}.$$
--
--   This is the one-step descent estimate from which the step-size window $\sigma \le \rho_k \le 2\rho_0 - \sigma$ of the method is derived.
--
--   **Formalization Note** The paper writes the bound as $\|\delta\|^2\{\rho^{-1} - f''(\xi, \delta, \delta)/2\|\delta\|^2\}$; for $\delta \ne 0$ this is the same quantity, and for $\delta = 0$ both sides are $0$. The multiplied-out form avoids dividing by $\|\delta\|^2 = 0$. The hypothesis that the segment lies in $\hat S$ is the condition under which the paper invokes Taylor's theorem; the paper leaves it implicit (its continuity argument supplies it). Here $y$ plays the role of the paper's $x_k$.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 710, PROOF, proof of (i), sentences 3–4

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, p. 710, proof of (i): with `δ = P(y - r∇f(y)) - y`, if the segment
`[y, P(y - r∇f(y))]` lies in `Ŝ`, then for some `t ∈ (0, 1)`,
`f(y) - f(y + δ) ≥ ‖δ‖² / r - f″(y + tδ, δ, δ) / 2` (Taylor's theorem with the second directional
Gâteaux derivative `d2`). -/
theorem taylor_estimate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (Shat : Set H) (ρ0 : ℝ) (hρ0 : 0 < ρ0)
    (hD : SecondDerivBound f Shat ρ0)
    (y : H) (hy : y ∈ C) (r : ℝ) (hr : 0 < r)
    (hseg : segment ℝ y (P (y - r • gradient f y)) ⊆ Shat) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      ‖P (y - r • gradient f y) - y‖ ^ 2 / r
          - d2 f (y + t • (P (y - r • gradient f y) - y)) (P (y - r • gradient f y) - y) / 2
        ≤ f y - f (P (y - r • gradient f y)) := by sorry

end GoldsteinProj.Conv
