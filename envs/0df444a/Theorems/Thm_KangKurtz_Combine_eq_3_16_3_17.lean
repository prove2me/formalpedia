-- Prove2me | Theorems.Thm_KangKurtz_Combine_eq_3_16_3_17
-- name    : KangKurtz.Combine.eq_3_16_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:41.215994+00:00
-- url     : https://prove2.me/theorems/63a2265d-72ff-458d-9746-c93d5ea9e62f
-- title:
--   §3.4, (3.16)–(3.17), p. 15 — the sign sets of c₁θ¹ + c₂θ² lie in the unions of those of θ¹ and θ²
-- statement:
--   Consider a reaction network with net changes $\zeta_k$, species exponents $\alpha_i\ge0$, reaction exponents $\beta_k$, and $\rho_k=\beta_k+\nu_k\cdot\alpha$. For $\theta\in[0,\infty)^{s_0}$ let $\Gamma^\pm_\theta$ be the reactions with $\pm\,\theta\cdot\zeta_k>0$.
--
--   Let $\theta^1,\theta^2\in[0,\infty)^{s_0}$ and $c_1,c_2>0$. Then
--   $$\Gamma^+_{c_1\theta^1+c_2\theta^2}\subseteq\Gamma^+_{\theta^1}\cup\Gamma^+_{\theta^2},\qquad \Gamma^-_{c_1\theta^1+c_2\theta^2}\subseteq\Gamma^-_{\theta^1}\cup\Gamma^-_{\theta^2},$$
--   and consequently
--   $$\max_{k\in\Gamma^+_{c_1\theta^1+c_2\theta^2}}\rho_k\le\max_{k\in\Gamma^+_{\theta^1}}\rho_k\vee\max_{k\in\Gamma^+_{\theta^2}}\rho_k, \tag{3.16}$$
--   $$\max_{k\in\Gamma^-_{c_1\theta^1+c_2\theta^2}}\rho_k\le\max_{k\in\Gamma^-_{\theta^1}}\rho_k\vee\max_{k\in\Gamma^-_{\theta^2}}\rho_k, \tag{3.17}$$
--   where $\vee$ is the maximum and a maximum over the empty set is $-\infty$.
--
--   These two inequalities are the upper halves of every sandwich used in Lemmas 3.6–3.8.
--
--   **Formalization Note.** Maxima are in `WithBot ℝ` and $\vee$ is `⊔`. The hypotheses $\alpha\ge0$ and $\theta^1,\theta^2\ge0$ are the paper's standing assumptions and are kept although the statement does not need them.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 15, §3.4, (3.16)–(3.17)

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

namespace KangKurtz.Combine

theorem eq_3_16_3_17 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    KangKurtz.SCC.GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂) ⊆ KangKurtz.SCC.GammaPlus ν ν' θ₁ ∪ KangKurtz.SCC.GammaPlus ν ν' θ₂ ∧
    KangKurtz.SCC.GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂) ⊆ KangKurtz.SCC.GammaMinus ν ν' θ₁ ∪ KangKurtz.SCC.GammaMinus ν ν' θ₂ ∧
    KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ≤
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁) ⊔ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₂) ∧
    KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ≤
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁) ⊔ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₂) := by sorry

end KangKurtz.Combine
