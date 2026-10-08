-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussIntegral_eq_of_homotopy
-- name    : HryniewiczCriterion.gaussIntegral_eq_of_homotopy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T20:46:25.83198+00:00
-- url     : https://prove2.me/theorems/9e5f123e-d5da-49db-9b97-e88954b9b74d
-- title:
--   The Gauss linking integral in a hyperplane is invariant under $C^2$ homotopies of disjoint loops
-- statement:
--   Let $N\in\mathbb{R}^4$ and let $A,B:\mathbb{R}\times\mathbb{R}\to\mathbb{R}^4$ be $C^2$ maps, $1$-periodic in the second variable, such that $A(\tau,s)\neq B(\tau,t)$ and $A(\tau,s)-B(\tau,t)\perp N$ for all $\tau,s,t$. Write $V(a,b,c)=\det(-N,a,b,c)$ (rows). Then the Gauss integral
--   $$I(\tau)=\int_0^1\!\!\int_0^1 \frac{V\big(\partial_sA(\tau,s),\ \partial_tB(\tau,t),\ A(\tau,s)-B(\tau,t)\big)}{|A(\tau,s)-B(\tau,t)|^3}\,dt\,ds$$
--   satisfies $I(0)=I(1)$.
--
--   Proof idea: with $u=A-B$ and $G(a,b,u)=V(a,b,u)/|u|^3$, one has pointwise
--   $$\partial_\tau G(A_s,B_t,u)=\partial_s G(u_\tau,B_t,u)-\partial_t G(A_s,u_\tau,u).$$
--   The mixed partials cancel by symmetry of second derivatives. The remaining terms vanish by the Cramer identity $\langle u,a\rangle V(u,b,c)+\langle u,b\rangle V(a,u,c)+\langle u,c\rangle V(a,b,u)=|u|^2V(a,b,c)$ for $u\perp N$; this is $\operatorname{div}(u/|u|^3)=0$. Integrate over $[0,1]^3$: the FTC in $\tau$ gives $I(1)-I(0)$, and by Fubini and periodicity the right-hand side integrates to $0$.
-- source:
--   Gauss linking integral and its homotopy invariance (Rolfsen, Knots and Links, 1976, Ch. 5D; Ricca–Nipoti, Gauss' linking number revisited, J. Knot Theory Ramifications 20 (2011)); used for linking numbers in Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077.

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.gaussIntegral_eq_of_homotopy (N : R4) (A B : ℝ → ℝ → R4)
    (hA : ContDiff ℝ 2 (Function.uncurry A)) (hB : ContDiff ℝ 2 (Function.uncurry B))
    (hAper : ∀ τ s, A τ (s + 1) = A τ s) (hBper : ∀ τ t, B τ (t + 1) = B τ t)
    (hN : ∀ τ s t, dot4 (A τ s - B τ t) N = 0) (hne : ∀ τ s t, A τ s ≠ B τ t) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        volumeIn N (deriv (A 0) s) (deriv (B 0) t) (A 0 s - B 0 t) /
          euclidNorm (A 0 s - B 0 t) ^ 3 =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        volumeIn N (deriv (A 1) s) (deriv (B 1) t) (A 1 s - B 1 t) /
          euclidNorm (A 1 s - B 1 t) ^ 3 := by sorry
