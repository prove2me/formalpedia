-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_comp_const_sub
-- name    : HryniewiczCriterion.gaussLinkingIntegral_comp_const_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:36:41.030262+00:00
-- url     : https://prove2.me/theorems/989d99ff-db92-48e9-98aa-55b3da32f104
-- title:
--   Reversing the first loop changes the sign of the Gauss linking integral
-- statement:
--   Let $\gamma_1:\mathbb{R}\to\mathbb{R}^4$ be $1$-periodic, let $\gamma_2$ be any loop, and let $c\in\mathbb{R}$. Traversing $\gamma_1$ backwards, $s\mapsto\gamma_1(c-s)$, reverses the sign:
--   $$\mathrm{Gauss}_N\big(s\mapsto\gamma_1(c-s),\ \gamma_2\big)=-\,\mathrm{Gauss}_N(\gamma_1,\gamma_2).$$
--   $\mathrm{Gauss}_N(\gamma_1,\gamma_2)$ denotes `gaussLinkingIntegral N γ₁ γ₂`, the Gauss double integral $\frac1{4\pi}\int_0^1\!\int_0^1\frac{\operatorname{vol}(A'(s),B'(t),A(s)-B(t))}{|A(s)-B(t)|^3}\,dt\,ds$ of the stereographic images $A=\sigma_N\circ\gamma_1$, $B=\sigma_N\circ\gamma_2$ from the pole $N$.
--
--   The velocity of the reversed loop is $-\gamma_1'(c-s)$, and the integrand is linear in the first velocity. Substituting $s\mapsto c-s$ and using periodicity gives the claim. No regularity hypothesis is needed. This is $\operatorname{lk}(-K_1,K_2)=-\operatorname{lk}(K_1,K_2)$.
-- source:
--   Standard (orientation reversal of the linking number), e.g. D. Rolfsen, Knots and Links, Ch. 5D

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_comp_const_sub (N : R4) (γ₁ γ₂ : ℝ → R4)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (c : ℝ) :
    gaussLinkingIntegral N (fun s => γ₁ (c - s)) γ₂ = -gaussLinkingIntegral N γ₁ γ₂ := by sorry
