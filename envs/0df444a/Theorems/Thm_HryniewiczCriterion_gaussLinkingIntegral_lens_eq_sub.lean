-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_lens_eq_sub
-- name    : HryniewiczCriterion.gaussLinkingIntegral_lens_eq_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T11:20:57.269179+00:00
-- url     : https://prove2.me/theorems/61c9f241-e71b-4d97-beed-4ba80a9ddae9
-- title:
--   Lens identity: the Gauss integral of a loop that sweeps a window forth along one curve and back along another is the difference of the two Gauss integrals
-- statement:
--   Let $N\in S^3$ and let $A_1,A_0,\Lambda,\gamma:\mathbb R\to S^3\subset\mathbb R^4$ be $C^2$ loops (with $A_1,A_0$ of period $1$) that avoid $N$, where each of $A_1,A_0,\Lambda$ is disjoint from $\gamma$. Let $d\le\tfrac12$ and $s(\sigma)=s_0-d\cos2\pi\sigma$, which sweeps $[s_0-d,s_0+d]$ forward for $\sigma\in[0,\tfrac12]$ and backward for $\sigma\in[\tfrac12,1]$. Suppose:
--   - $A_1=A_0$ near every point of $[s_0+d,\,s_0-d+1]$ (the curves differ only inside the window);
--   - $\Lambda=A_1\circ s$ near every point of $[0,\tfrac12]$;
--   - $\Lambda=A_0\circ s$ near every point of $[\tfrac12,1]$.
--
--   Then $\mathrm{Gauss}_N(\Lambda,\gamma)=\mathrm{Gauss}_N(A_1,\gamma)-\mathrm{Gauss}_N(A_0,\gamma)$ (`gaussLinkingIntegral`, stereographic projection from $N$).
--
--   Proof (substitution only, no homotopy). After stereographic projection the outer integrand is $J_A(x)\,=\,\int_0^1 f(A(x),A'(x),\gamma(t),\gamma'(t))\,dt$, which is linear in the velocity $A'(x)$. On $[0,\tfrac12]$ we have $\Lambda'(\sigma)=s'(\sigma)A_1'(s(\sigma))$, so substituting $x=s(\sigma)$ gives $\int_0^{1/2}J_\Lambda=\int_{s_0-d}^{s_0+d}J_{A_1}$. Likewise $\int_{1/2}^1J_\Lambda=-\int_{s_0-d}^{s_0+d}J_{A_0}$. By periodicity, $\int_0^1J_{A_i}=\int_{s_0-d}^{s_0+d}J_{A_i}+\int_{s_0+d}^{s_0-d+1}J_{A_i}$, and the last integrals agree for $i=0,1$.
-- source:
--   Elementary (change of variables in the Gauss linking integral); used for the residue formula, cf. D. Rolfsen, Knots and Links, Ch. 5D

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_lens_eq_sub (N : R4) (hN : euclidNorm N = 1)
    (A₁ A₀ Λ γ : ℝ → R4) (s₀ d : ℝ) (hd : d ≤ 1 / 2)
    (hA₁ : ContDiff ℝ 2 A₁) (hA₀ : ContDiff ℝ 2 A₀) (hΛ : ContDiff ℝ 2 Λ) (hγ : ContDiff ℝ 2 γ)
    (hA₁per : ∀ x, A₁ (x + 1) = A₁ x) (hA₀per : ∀ x, A₀ (x + 1) = A₀ x)
    (hA₁unit : ∀ x, euclidNorm (A₁ x) = 1) (hA₀unit : ∀ x, euclidNorm (A₀ x) = 1)
    (hΛunit : ∀ x, euclidNorm (Λ x) = 1) (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (hA₁N : ∀ x, A₁ x ≠ N) (hA₀N : ∀ x, A₀ x ≠ N) (hΛN : ∀ x, Λ x ≠ N) (hγN : ∀ t, γ t ≠ N)
    (hA₁γ : ∀ x t, A₁ x ≠ γ t) (hA₀γ : ∀ x t, A₀ x ≠ γ t) (hΛγ : ∀ x t, Λ x ≠ γ t)
    (hagree : ∀ x ∈ Set.Icc (s₀ + d) (s₀ - d + 1), Filter.EventuallyEq (nhds x) A₁ A₀)
    (hΛ₁ : ∀ σ ∈ Set.Icc (0 : ℝ) (1 / 2),
      Filter.EventuallyEq (nhds σ) Λ fun σ => A₁ (s₀ - d * Real.cos (2 * Real.pi * σ)))
    (hΛ₀ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      Filter.EventuallyEq (nhds σ) Λ fun σ => A₀ (s₀ - d * Real.cos (2 * Real.pi * σ))) :
    gaussLinkingIntegral N Λ γ = gaussLinkingIntegral N A₁ γ - gaussLinkingIntegral N A₀ γ := by sorry
