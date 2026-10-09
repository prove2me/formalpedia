-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_comp_mul_nat
-- name    : HryniewiczCriterion.gaussLinkingIntegral_comp_mul_nat
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T17:59:16.536437+00:00
-- url     : https://prove2.me/theorems/fc36325c-311a-46bc-aa01-48701ff0fb54
-- title:
--   The Gauss linking integral is multiplied by $k$ when the second loop is traversed $k$ times
-- statement:
--   Let $\gamma_1,\gamma_2:\mathbb{R}\to S^3$ be disjoint $C^2$ loops of period $1$, and let $N\in S^3$ miss both. For every $k\in\mathbb{N}$,
--   $$\mathrm{Gauss}_N\big(\gamma_1,\ t\mapsto\gamma_2(kt)\big)=k\cdot\mathrm{Gauss}_N(\gamma_1,\gamma_2).$$
--
--   Here $\mathrm{Gauss}_N$ is `gaussLinkingIntegral`, the Gauss double integral after stereographic projection from $N$. The integrand is linear in the velocity of the second loop, so substituting $t\mapsto kt$ turns $\int_0^1dt$ into $\int_0^k$. By periodicity this is $k$ copies of $\int_0^1$. For $k=0$ both sides vanish, because the second loop is constant.
-- source:
--   Elementary (change of variables in the Gauss linking integral); used for multiply covered orbits in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Definition 1.5 and Lemma 3.12.

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_comp_mul_nat (N : R4) (γ₁ γ₂ : ℝ → R4)
    (h₁ : ContDiff ℝ 2 γ₁) (h₂ : ContDiff ℝ 2 γ₂)
    (hper₁ : ∀ s, γ₁ (s + 1) = γ₁ s) (hper₂ : ∀ s, γ₂ (s + 1) = γ₂ s)
    (hunit₁ : ∀ s, euclidNorm (γ₁ s) = 1) (hunit₂ : ∀ s, euclidNorm (γ₂ s) = 1)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) (hN : euclidNorm N = 1) (hNγ : ∀ s, γ₁ s ≠ N ∧ γ₂ s ≠ N)
    (k : ℕ) :
    gaussLinkingIntegral N γ₁ (fun t => γ₂ (k * t)) = k * gaussLinkingIntegral N γ₁ γ₂ := by sorry
