-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_eq_of_pole_path
-- name    : HryniewiczCriterion.gaussLinkingIntegral_eq_of_pole_path
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T20:46:25.209193+00:00
-- url     : https://prove2.me/theorems/82c3abaa-57c9-42ba-8ce2-45d325ee2dc0
-- title:
--   The Gauss linking integral is unchanged when the stereographic pole moves along a path avoiding both loops
-- statement:
--   Let $\gamma_1,\gamma_2:\mathbb{R}\to S^3\subset\mathbb{R}^4$ be $C^2$, $1$-periodic loops with disjoint images. Let $P:\mathbb{R}\to S^3$ be a $C^2$ path of poles that misses both loops, $P(\tau)\notin\gamma_1(\mathbb{R})\cup\gamma_2(\mathbb{R})$, and is never antipodal to $P(0)$, i.e. $P(\tau)\neq -P(0)$. Then the Gauss linking integrals after stereographic projection from $P(0)$ and from $P(1)$ agree:
--   $$\operatorname{gaussLinkingIntegral}(P(0),\gamma_1,\gamma_2)=\operatorname{gaussLinkingIntegral}(P(1),\gamma_1,\gamma_2).$$
--   Proof idea: let $N=P(0)$ and $R_\tau=S_{P(\tau)+N}\circ S_{P(\tau)}$, where $S_v$ is the reflection in $v^\perp$. Then $R_\tau\in SO(4)$ depends $C^2$ on $\tau$ and $R_\tau P(\tau)=N$. Stereographic projection is equivariant, $\sigma_{N}(R_\tau y)=R_\tau\sigma_{P(\tau)}(y)$, and the integrand $\det(-N,a,b,c)/|c|^3$ is invariant under $R_\tau$. So the integral from the pole $P(\tau)$ equals the fixed-pole Gauss integral of the loops $\sigma_N\circ R_\tau\circ\gamma_i$. These form a $C^2$ homotopy of disjoint loops in $N^\perp$, so the integral is constant (`gaussIntegral_eq_of_homotopy`).
-- source:
--   Gauss linking integral and its homotopy invariance (Rolfsen, Knots and Links, 1976, Ch. 5D; Ricca–Nipoti, Gauss' linking number revisited, J. Knot Theory Ramifications 20 (2011)); used for linking numbers in Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077.

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.gaussLinkingIntegral_eq_of_pole_path (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t)
    (P : ℝ → R4) (hP : ContDiff ℝ 2 P) (hPunit : ∀ τ, euclidNorm (P τ) = 1)
    (hPγ : ∀ τ s, γ₁ s ≠ P τ ∧ γ₂ s ≠ P τ) (hopp : ∀ τ, P τ + P 0 ≠ 0) :
    gaussLinkingIntegral (P 0) γ₁ γ₂ = gaussLinkingIntegral (P 1) γ₁ γ₂ := by sorry
