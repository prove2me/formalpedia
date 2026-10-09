-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_circle_immersion
-- name    : HryniewiczCriterion.gaussLinkingIntegral_circle_immersion
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T19:10:44.003757+00:00
-- url     : https://prove2.me/theorems/011206a6-6a6d-4df0-b319-6bcb8994c65a
-- title:
--   A periodic immersion onto the circle is a $k$-fold cover with $k\neq0$, and the Gauss integral of its image loop is $k$ times that of the standard circle
-- statement:
--   Let $u:\mathbb{R}\to S^1$ be a $C^2$ map of period $1$ with $u'\neq0$ everywhere. Then $u$ is onto $S^1$, and $u(s)=(\cos2\pi\theta(s),\sin2\pi\theta(s))$ for a lift $\theta$ with $\theta(s+1)=\theta(s)+k$, $k\in\mathbb{Z}\setminus\{0\}$ (if $k=0$, $\theta$ would be periodic, hence have a critical point, where $u'=0$).
--
--   Let $E$ be $C^2$ near $S^1$ with $|E|=1$ on $S^1$, let $\gamma:\mathbb{R}\to S^3$ be a $C^2$ loop of period $1$ missing $E(u(\mathbb{R}))=E(S^1)$, and let $N\in S^3$ miss both. Then
--   $$\mathrm{Gauss}_N(E\circ u,\gamma)=k\cdot\mathrm{Gauss}_N\big(E\circ c,\gamma\big),\qquad c(s)=(\cos2\pi s,\sin2\pi s),$$
--   with `gaussLinkingIntegral` as $\mathrm{Gauss}_N$.
--
--   Suggested proof. The straight-line homotopy $\theta_\tau=(1-\tau)\theta+\tau ks$ keeps the loops $E\circ c\circ\theta_\tau$ inside $E(S^1)$, so homotopy invariance (`gaussIntegral_eq_of_homotopy`) gives $\mathrm{Gauss}_N(E\circ u,\gamma)=\mathrm{Gauss}_N(E\circ c(k\,\cdot),\gamma)$. For $k>0$ use the symmetry of the Gauss integrand and `gaussLinkingIntegral_comp_mul_nat`; for $k<0$ additionally reverse the loop, which changes the sign.
-- source:
--   Elementary (lifting of circle maps and the multiplicativity of the Gauss integral); used for the boundary parametrization in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Lemma 3.12.

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_circle_immersion (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hCU : unitCircle ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ unitCircle, euclidNorm (E v) = 1)
    (u : ℝ → Plane) (hu : ContDiff ℝ 2 u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hu' : ∀ s, deriv u s ≠ 0)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hbd : ∀ s t, E (u s) ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N) (hNE : ∀ s, E (u s) ≠ N) :
    (∀ w ∈ unitCircle, ∃ s, u s = w) ∧ ∃ k : ℤ, k ≠ 0 ∧
      gaussLinkingIntegral N (fun s => E (u s)) γ =
        k * gaussLinkingIntegral N (fun s => E (circlePoint s)) γ := by sorry
