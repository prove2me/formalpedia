-- Prove2me | Theorems.Thm_KangKurtz_Combine_lemma_3_6
-- name    : KangKurtz.Combine.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:14.736888+00:00
-- url     : https://prove2.me/theorems/cda58e0e-ca90-44ae-9201-f4762930652a
-- title:
--   Lemma 3.6, p. 17 — if θ¹ is balanced at a level above every ρ_k of Γ^±_{θ²}, then c₁θ¹ + c₂θ² is balanced
-- statement:
--   Consider a reaction network with net changes $\zeta_k$, species exponents $\alpha_i\ge0$, reaction exponents $\beta_k$ and $\rho_k=\beta_k+\nu_k\cdot\alpha$. For $\theta\in[0,\infty)^{s_0}$ let $\Gamma^\pm_\theta$ be the reactions with $\pm\,\theta\cdot\zeta_k>0$; maxima over the empty set are $-\infty$.
--
--   Let $\theta^1,\theta^2\in[0,\infty)^{s_0}$ satisfy
--   $$\max_{k\in\Gamma^-_{\theta^1}}\rho_k=\max_{k\in\Gamma^+_{\theta^1}}\rho_k>\max_{k\in\Gamma^+_{\theta^2}\cup\Gamma^-_{\theta^2}}\rho_k. \tag{3.31}$$
--   Then for all $c_1,c_2>0$ the balance equation (3.7) holds for $c_1\theta^1+c_2\theta^2$:
--   $$\max_{k\in\Gamma^-_{c_1\theta^1+c_2\theta^2}}\rho_k=\max_{k\in\Gamma^+_{c_1\theta^1+c_2\theta^2}}\rho_k .$$
--
--   The strict inequality in (3.31) forces $\Gamma^+_{\theta^1}\neq\emptyset$; the right-hand side may be $-\infty$. This lemma handles the case of Lemma 3.8 in which both vectors are balanced at different levels.
--
--   **Formalization Note.** (3.31) is split into the equality and the strict inequality, both in `WithBot ℝ`; the maximum on the right is over the union $\Gamma^+_{\theta^2}\cup\Gamma^-_{\theta^2}$, as printed.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 17, Lemma 3.6, (3.31)

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

namespace KangKurtz.Combine

theorem lemma_3_6 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (h331_eq : KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁) = KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁))
    (h331_lt : KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₂ ∪ KangKurtz.SCC.GammaMinus ν ν' θ₂) <
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    KangKurtz.SCC.Balance ν ν' α β (c₁ • θ₁ + c₂ • θ₂) := by sorry

end KangKurtz.Combine
