-- Prove2me | Theorems.Thm_KangKurtz_Combine_lemma_3_7
-- name    : KangKurtz.Combine.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:26.211178+00:00
-- url     : https://prove2.me/theorems/728c5bc3-9f21-4178-a52b-aeb547499284
-- title:
--   Lemma 3.7, p. 18 — balance (3.7) for θ¹ and (3.8) for θ² give Condition 3.2 for c₁θ¹ + c₂θ²
-- statement:
--   Consider a reaction network with net changes $\zeta_k$, species exponents $\alpha_i\ge0$, reaction exponents $\beta_k$ and $\rho_k=\beta_k+\nu_k\cdot\alpha$, with sign sets $\Gamma^\pm_\theta$ and $\gamma_\theta$ as in Condition 3.2.
--
--   Fix $\gamma\in\mathbb R$ and let $\theta^1,\theta^2\in[0,\infty)^{s_0}$. Suppose the balance equation (3.7) holds for $\theta^1$,
--   $$\max_{k\in\Gamma^-_{\theta^1}}\rho_k=\max_{k\in\Gamma^+_{\theta^1}}\rho_k,$$
--   and the time-scale constraint (3.8) holds for $\theta^2$, $\gamma\le\gamma_{\theta^2}$. Then for all $c_1,c_2>0$, Condition 3.2 holds for $c_1\theta^1+c_2\theta^2$: either (3.7) or (3.8) holds for it.
--
--   This is the mixed case of Lemma 3.8.
--
--   **Formalization Note.** $\theta^1,\theta^2\ge0$ is the standing domain of Condition 3.2 on p. 10 and is kept as a hypothesis.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 18, Lemma 3.7

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

namespace KangKurtz.Combine

theorem lemma_3_7 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (γ : ℝ) (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (hbal : KangKurtz.SCC.Balance ν ν' α β θ₁) (hts : TimeScale ν ν' α β γ θ₂)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    Cond32 ν ν' α β γ (c₁ • θ₁ + c₂ • θ₂) := by sorry

end KangKurtz.Combine
