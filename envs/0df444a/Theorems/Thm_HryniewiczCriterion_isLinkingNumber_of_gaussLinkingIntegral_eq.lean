-- Prove2me | Theorems.Thm_HryniewiczCriterion_isLinkingNumber_of_gaussLinkingIntegral_eq
-- name    : HryniewiczCriterion.isLinkingNumber_of_gaussLinkingIntegral_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T19:37:46.579634+00:00
-- url     : https://prove2.me/theorems/cd1d24f4-0a81-484b-9605-91553b008ff8
-- title:
--   The Gauss linking integral of two disjoint loops in $S^3$ does not depend on the stereographic pole
-- statement:
--   Let $\gamma_1,\gamma_2:\mathbb{R}\to S^3\subset\mathbb{R}^4$ be $C^2$, $1$-periodic loops with disjoint images. Let $N\in S^3$ be a pole missing both loops, and suppose the Gauss linking integral of the stereographic images,
--   $$\frac{1}{4\pi}\int_0^1\!\!\int_0^1 \frac{\det\big(-N,\ A'(s),\ B'(t),\ A(s)-B(t)\big)}{|A(s)-B(t)|^3}\,dt\,ds,\qquad A=\sigma_N\circ\gamma_1,\ B=\sigma_N\circ\gamma_2,$$
--   equals the integer $n$. Then $n$ is the linking number of $\gamma_1,\gamma_2$ in the sense of `IsLinkingNumber`: the integral equals $n$ for every pole $N'\in S^3$ that misses both loops.
--
--   Proof idea: the Gauss integral is constant along any $C^2$ homotopy of the pair of loops that keeps them disjoint (its $\tau$-derivative is the integral of an exact form on the torus, because $u\mapsto u/|u|^3$ is divergence free). Moving the pole along a path $N_\tau$ in $S^3\setminus(\gamma_1\cup\gamma_2)$ and composing with rotations $R_\tau\in SO(4)$, $R_\tau N_\tau=N$, turns the change of pole into such a homotopy, since the integrand is invariant under rotations. The complement of two $C^1$ curves in $S^3$ is path connected: the great-circle cones over the curves from a point are images of $2$-dimensional sets, so they have measure zero and a midpoint avoiding them exists.
-- source:
--   Gauss linking integral and its independence of the projection (Rolfsen, Knots and Links, 1976, Ch. 5D; Ricca–Nipoti, Gauss' linking number revisited, J. Knot Theory Ramifications 20 (2011)).

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.isLinkingNumber_of_gaussLinkingIntegral_eq (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N)
    (n : ℤ) (hG : gaussLinkingIntegral N γ₁ γ₂ = n) :
    IsLinkingNumber γ₁ γ₂ n := by sorry
