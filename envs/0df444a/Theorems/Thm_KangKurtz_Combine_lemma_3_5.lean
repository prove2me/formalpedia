-- Prove2me | Theorems.Thm_KangKurtz_Combine_lemma_3_5
-- name    : KangKurtz.Combine.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:35.197994+00:00
-- url     : https://prove2.me/theorems/8c9ad522-8688-49c8-a907-14892c1e6858
-- title:
--   Lemma 3.5, p. 17 — the time-scale constraint (3.8) is preserved by positive combinations
-- statement:
--   Consider a reaction network with net changes $\zeta_k$, species exponents $\alpha_i\ge0$, reaction exponents $\beta_k$ and $\rho_k=\beta_k+\nu_k\cdot\alpha$. For $\theta\in[0,\infty)^{s_0}$ let $\Gamma^\pm_\theta$ be the reactions with $\pm\,\theta\cdot\zeta_k>0$, and
--   $$\gamma_\theta=\max_{i:\theta_i>0}\alpha_i-\max_{k\in\Gamma^+_\theta\cup\Gamma^-_\theta}\rho_k\qquad(=+\infty\text{ if }\Gamma^+_\theta\cup\Gamma^-_\theta=\emptyset).$$
--
--   Fix $\gamma\in\mathbb R$ and suppose the time-scale constraint (3.8), $\gamma\le\gamma_{\theta^j}$, holds for $\theta^1,\dots,\theta^m\in[0,\infty)^{s_0}$. Then for all $c_j>0$, $j=1,\dots,m$,
--   $$\gamma\le\gamma_\theta,\qquad \theta=\sum_{j=1}^m c_j\theta^j .$$
--
--   This is the case of Lemma 3.8 in which both vectors satisfy (3.8).
--
--   **Formalization Note.** The family is indexed by `Fin m`; for $m=0$ the sum is $\theta=0$, for which $\gamma_0=+\infty$. $\gamma_\theta$ is an `EReal` defined by cases (see the setting definition).
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 17, Lemma 3.5

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

namespace KangKurtz.Combine

theorem lemma_3_5 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (γ : ℝ) {m : ℕ} (θs : Fin m → Fin s → ℝ) (hθs : ∀ j i, 0 ≤ θs j i)
    (hts : ∀ j, TimeScale ν ν' α β γ (θs j))
    (c : Fin m → ℝ) (hc : ∀ j, 0 < c j) :
    TimeScale ν ν' α β γ (∑ j, c j • θs j) := by sorry

end KangKurtz.Combine
