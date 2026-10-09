-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_comp_add_right
-- name    : HryniewiczCriterion.gaussLinkingIntegral_comp_add_right
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:38:39.248136+00:00
-- url     : https://prove2.me/theorems/f07830ef-2d9c-46c6-b4b4-e903f25ff8c6
-- title:
--   Shifting the parameter of the second loop does not change the Gauss linking integral
-- statement:
--   Let $\gamma_2:\mathbb{R}\to\mathbb{R}^4$ be $1$-periodic, let $\gamma_1$ be any loop, and let $c\in\mathbb{R}$. Then
--   $$\mathrm{Gauss}_N\big(\gamma_1,\ t\mapsto\gamma_2(t+c)\big)=\mathrm{Gauss}_N(\gamma_1,\gamma_2).$$
--   $\mathrm{Gauss}_N(\gamma_1,\gamma_2)$ denotes `gaussLinkingIntegral N γ₁ γ₂`, the Gauss double integral $\frac1{4\pi}\int_0^1\!\int_0^1\frac{\operatorname{vol}(A'(s),B'(t),A(s)-B(t))}{|A(s)-B(t)|^3}\,dt\,ds$ of the stereographic images $A=\sigma_N\circ\gamma_1$, $B=\sigma_N\circ\gamma_2$ from the pole $N$.
--
--   The inner integrand is $1$-periodic in $t$, so an integral over any interval of length $1$ gives the same value. No regularity or disjointness hypothesis is needed: the identity holds for the defining expression as it stands.
-- source:
--   Elementary (periodicity of the Gauss integrand); used to move a crossing to $t=0$ in U. Hryniewicz, arXiv:1105.2077, Lemma 3.12

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_comp_add_right (N : R4) (γ₁ γ₂ : ℝ → R4)
    (hper₂ : ∀ t, γ₂ (t + 1) = γ₂ t) (c : ℝ) :
    gaussLinkingIntegral N γ₁ (fun t => γ₂ (t + c)) = gaussLinkingIntegral N γ₁ γ₂ := by sorry
