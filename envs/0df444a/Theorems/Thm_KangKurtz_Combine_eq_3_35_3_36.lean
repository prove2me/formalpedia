-- Prove2me | Theorems.Thm_KangKurtz_Combine_eq_3_35_3_36
-- name    : KangKurtz.Combine.eq_3_35_3_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:25.799986+00:00
-- url     : https://prove2.me/theorems/624ff1b5-a8b5-4bf2-bf06-5ea25f9a8a13
-- title:
--   Proof of Lemma 3.8, (3.35)–(3.36), p. 19 — sandwich bounds when Γ⁻_{θ¹} ∩ Γ⁺_{θ²} = ∅
-- statement:
--   Consider a reaction network with net changes $\zeta_k$, species exponents $\alpha_i\ge0$, reaction exponents $\beta_k$ and $\rho_k=\beta_k+\nu_k\cdot\alpha$. For $\theta\in[0,\infty)^{s_0}$ let $\Gamma^\pm_\theta$ be the reactions with $\pm\,\theta\cdot\zeta_k>0$; maxima over the empty set are $-\infty$ and $\vee$ denotes the maximum.
--
--   Let $\theta^1,\theta^2\in[0,\infty)^{s_0}$ with $\Gamma^-_{\theta^1}\cap\Gamma^+_{\theta^2}=\emptyset$, and $c_1,c_2>0$. Then
--   $$\max_{k\in\Gamma^-_{\theta^1}}\rho_k\le\max_{k\in\Gamma^-_{c_1\theta^1+c_2\theta^2}}\rho_k\le\max_{k\in\Gamma^-_{\theta^1}}\rho_k\vee\max_{k\in\Gamma^-_{\theta^2}}\rho_k, \tag{3.35}$$
--   $$\max_{k\in\Gamma^+_{\theta^2}}\rho_k\le\max_{k\in\Gamma^+_{c_1\theta^1+c_2\theta^2}}\rho_k\le\max_{k\in\Gamma^+_{\theta^1}}\rho_k\vee\max_{k\in\Gamma^+_{\theta^2}}\rho_k. \tag{3.36}$$
--
--   When all four maxima of $\theta^1$ and $\theta^2$ coincide (the situation (3.34) of the paper), these bounds collapse to equalities and give the balance equation for $c_1\theta^1+c_2\theta^2$; this is the one case of Lemma 3.8 not covered by Lemmas 3.5–3.7.
--
--   **Formalization Note.** All maxima are in `WithBot ℝ`; the conclusion is the conjunction of the four inequalities.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 19, §3.4, proof of Lemma 3.8, (3.35)–(3.36)

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

namespace KangKurtz.Combine

theorem eq_3_35_3_36 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (hdisj : Disjoint (KangKurtz.SCC.GammaMinus ν ν' θ₁) (KangKurtz.SCC.GammaPlus ν ν' θ₂))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁) ≤ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ∧
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ≤
        KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁) ⊔ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₂)) ∧
    (KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₂) ≤ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ∧
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ≤
        KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁) ⊔ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₂)) := by sorry

end KangKurtz.Combine
