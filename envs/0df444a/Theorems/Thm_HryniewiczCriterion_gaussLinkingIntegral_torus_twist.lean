-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_torus_twist
-- name    : HryniewiczCriterion.gaussLinkingIntegral_torus_twist
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T22:18:10.520155+00:00
-- url     : https://prove2.me/theorems/f18d6df3-4555-4902-a1ff-66580effee9e
-- title:
--   Gauss linking integral with a $(1,k)$-curve on a torus around a loop: twisting formula
-- statement:
--   Let $\gamma:\mathbb{R}\to S^3$ be a $C^2$ loop, $\gamma(s+1)=\gamma(s)$, and let $P:\mathbb{R}^2\to S^3$ be a $C^2$ torus, $1$-periodic in $t$ and $2\pi$-periodic in $\varphi$, disjoint from $\gamma$. Let $N\in S^3$ be a pole missing both. Let $\theta:\mathbb{R}\to\mathbb{R}$ be $C^2$ with
--   $$\theta(t+1)=\theta(t)+2\pi k,\qquad k\in\mathbb{Z}.$$
--   Then, for the Gauss linking integral after stereographic projection from $N$,
--   $$\mathrm{Gauss}_N\big(\gamma,\ t\mapsto P(t,\theta(t))\big)=\mathrm{Gauss}_N\big(\gamma,\ t\mapsto P(t,0)\big)+k\cdot\mathrm{Gauss}_N\big(\gamma,\ \varphi\mapsto P(0,2\pi\varphi)\big).$$
--   Proof: vary the open arcs $B_\tau(t)=P(t,\tau\theta(t))$, $\tau\in[0,1]$. The pointwise closedness identity of the Gauss $2$-form gives $\partial_\tau f=\partial_sP_s-\partial_tQ_t$. The $s$-term integrates to $0$ by periodicity of $\gamma$. The $t$-term leaves only the boundary terms at $t=0,1$, which sweep the meridian $\varphi\mapsto P(0,\varphi)$ from $\theta(0)$ to $\theta(0)+2\pi k$, that is, $k$ full turns.
-- source:
--   D. Rolfsen, Knots and Links, Publish or Perish, 1976, Ch. 5D (linking number via the Gauss integral; a meridian links its knot once; framings and the twisting of push-offs); used for self-linking numbers in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 1.5.

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.gaussLinkingIntegral_torus_twist (N : R4) (hN : euclidNorm N = 1) (γ : ℝ → R4) (P : ℝ → ℝ → R4)
    (hγ : ContDiff ℝ 2 γ) (hP : ContDiff ℝ 2 (Function.uncurry P))
    (hγper : ∀ s, γ (s + 1) = γ s) (hPper₁ : ∀ t φ, P (t + 1) φ = P t φ)
    (hPper₂ : ∀ t φ, P t (φ + 2 * Real.pi) = P t φ)
    (hγunit : ∀ s, euclidNorm (γ s) = 1) (hPunit : ∀ t φ, euclidNorm (P t φ) = 1)
    (hγN : ∀ s, γ s ≠ N) (hPN : ∀ t φ, P t φ ≠ N) (hne : ∀ s t φ, γ s ≠ P t φ)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 2 θ) (k : ℤ) (hθper : ∀ t, θ (t + 1) = θ t + 2 * Real.pi * k) :
    gaussLinkingIntegral N γ (fun t => P t (θ t)) =
      gaussLinkingIntegral N γ (fun t => P t 0) +
        k * gaussLinkingIntegral N γ (fun φ => P 0 (2 * Real.pi * φ)) := by sorry
