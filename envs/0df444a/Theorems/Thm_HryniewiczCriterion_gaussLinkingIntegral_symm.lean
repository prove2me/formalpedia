-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_symm
-- name    : HryniewiczCriterion.gaussLinkingIntegral_symm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:36:35.540538+00:00
-- url     : https://prove2.me/theorems/9be64c9a-de0c-4992-9f24-98170c6b33e7
-- title:
--   The Gauss linking integral is symmetric in its two loops
-- statement:
--   Let $\gamma_1,\gamma_2:\mathbb{R}\to S^3$ be disjoint $C^1$ loops and let $N\in S^3$ miss both. Then
--   $$\mathrm{Gauss}_N(\gamma_1,\gamma_2)=\mathrm{Gauss}_N(\gamma_2,\gamma_1).$$
--   $\mathrm{Gauss}_N(\gamma_1,\gamma_2)$ denotes `gaussLinkingIntegral N γ₁ γ₂`, the Gauss double integral $\frac1{4\pi}\int_0^1\!\int_0^1\frac{\operatorname{vol}(A'(s),B'(t),A(s)-B(t))}{|A(s)-B(t)|^3}\,dt\,ds$ of the stereographic images $A=\sigma_N\circ\gamma_1$, $B=\sigma_N\circ\gamma_2$ from the pole $N$.
--
--   The integrand is symmetric under exchanging the loops: $\operatorname{vol}(b,a,-u)=\operatorname{vol}(a,b,u)$ (one row swap and one sign change) and $|-u|=|u|$. The integrand is continuous on $[0,1]^2$ because the loops are disjoint, so Fubini's theorem exchanges the order of integration. This is the symmetry $\operatorname{lk}(K_1,K_2)=\operatorname{lk}(K_2,K_1)$ of the linking number in $S^3$.
-- source:
--   Standard (symmetry of the Gauss linking integral), e.g. D. Rolfsen, Knots and Links, Ch. 5D

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_symm (N : R4) (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 1 γ₁) (h₂ : ContDiff ℝ 1 γ₂)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N) :
    gaussLinkingIntegral N γ₁ γ₂ = gaussLinkingIntegral N γ₂ γ₁ := by sorry
