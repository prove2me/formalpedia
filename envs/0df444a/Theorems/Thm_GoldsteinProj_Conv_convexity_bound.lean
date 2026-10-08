-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_convexity_bound
-- name    : GoldsteinProj.Conv.convexity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:16.505204+00:00
-- url     : https://prove2.me/theorems/533727f3-2fcf-495b-b9b2-7e65872eb550
-- title:
--   Proofs of (iii), (v), p. 710 — f(x) ≧ f(y) + [∇f(y), x − y] + (1/2)μ‖x − y‖² for x, y ∈ S under the hypothesis of (iii)
-- statement:
--   Let $H$ be a real Hilbert space with inner product $[\cdot,\cdot]$, $C \subseteq H$, $f : H \to \mathbb R$, $x_0 \in H$ and $S = \{x \in C : f(x) \le f(x_0)\}$. Let $\hat S$ contain the convex hull of $S$, and assume that at every $x \in \hat S$ the function $f$ is Fréchet differentiable and $f''(x, h, h)$ exists in the sense of Gâteaux for every $h$ (with $|f''(x,h,h)| \le \|h\|^2/\rho_0$). Assume the hypothesis of part (iii): $S$ is convex and, for some $\mu \ge 0$, $f''(x, h, h) \ge \mu \|h\|^2$ for all $x \in S$, $h \in H$. Then for all $y, w \in S$,
--   $$f(w) \;\ge\; f(y) + [\nabla f(y),\, w - y] + \tfrac12 \mu \|w - y\|^2.$$
--
--   With $\mu = 0$ this is the gradient inequality $f(z) - f(x_k) \ge [\nabla f_k, z - x_k]$ used in the proof of (iii); with $\mu > 0$ it is the strong-convexity bound used twice in the proof of (v).
--
--   **Formalization Note** Only the existence parts of the hypothesis on $\hat S$ are used; neither openness of $\hat S$ nor a projection or an iteration is involved.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 710, PROOF, proof of (iii) (second sentence) and proof of (v) (first and fifth sentences)

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, p. 710, proofs of (iii) and (v): under the hypothesis of (iii)
(`S` convex, `f″(x, h, h) ≥ μ‖h‖²` on `S`), every `y, w ∈ S` satisfy
`f(w) ≥ f(y) + ⟪∇f(y), w - y⟫ + (1/2) μ ‖w - y‖²`. -/
theorem convexity_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (C : Set H) (x0 : H)
    (Shat : Set H) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hD : SecondDerivBound f Shat ρ0)
    (μ : ℝ) (hconv : ConvexityHyp f C x0 μ) :
    ∀ y ∈ levelSet f C x0, ∀ w ∈ levelSet f C x0,
      f y + ⟪gradient f y, w - y⟫ + (1 / 2) * μ * ‖w - y‖ ^ 2 ≤ f w := by sorry

end GoldsteinProj.Conv
