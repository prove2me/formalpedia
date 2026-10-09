-- Prove2me | Theorems.Thm_KangKurtz_Combine_lemma_3_8
-- name    : KangKurtz.Combine.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:42.112141+00:00
-- url     : https://prove2.me/theorems/ed916173-316e-41fe-b62b-5b9b01678322
-- title:
--   Lemma 3.8, p. 18 — Condition 3.2 and the balance equation (3.7) pass to c₁θ¹ + c₂θ² when Γ⁺_{θ¹} ∩ Γ⁻_{θ²} = ∅ or Γ⁻_{θ¹} ∩ Γ⁺_{θ²} = ∅
-- statement:
--   Consider a reaction network with $s_0$ species and $r_0$ reactions, net changes $\zeta_k=\nu'_k-\nu_k$, species exponents $\alpha_i\ge0$, reaction exponents $\beta_k\in\mathbb R$, and $\rho_k=\beta_k+\nu_k\cdot\alpha$. For $\theta\in[0,\infty)^{s_0}$ let $\Gamma^+_\theta=\{k:\theta\cdot\zeta_k>0\}$, $\Gamma^-_\theta=\{k:\theta\cdot\zeta_k<0\}$ (maxima over the empty set are $-\infty$). Fix $\gamma\in\mathbb R$. **Condition 3.2** holds for $\theta$ if
--   $$\max_{k\in\Gamma^-_\theta}\rho_k=\max_{k\in\Gamma^+_\theta}\rho_k \tag{3.7}$$
--   or
--   $$\gamma\le\gamma_\theta\equiv\max_{i:\theta_i>0}\alpha_i-\max_{k\in\Gamma^+_\theta\cup\Gamma^-_\theta}\rho_k \tag{3.8}$$
--   (with $\gamma_\theta=+\infty$ when $\Gamma^+_\theta\cup\Gamma^-_\theta=\emptyset$).
--
--   Let $\theta^1,\theta^2\in[0,\infty)^{s_0}$ and $c_1,c_2>0$, and suppose
--   $$\Gamma^+_{\theta^1}\cap\Gamma^-_{\theta^2}=\emptyset\quad\text{or}\quad\Gamma^-_{\theta^1}\cap\Gamma^+_{\theta^2}=\emptyset .$$
--   Then:
--
--   1. if Condition 3.2 holds for $\theta^1$ and for $\theta^2$, it holds for $c_1\theta^1+c_2\theta^2$;
--   2. if the balance equation (3.7) holds for $\theta^1$ and for $\theta^2$, it holds for $c_1\theta^1+c_2\theta^2$.
--
--   Some hypothesis beyond Condition 3.2 for $\theta^1$ and $\theta^2$ is needed: the paper notes (p. 18) that for its example system (3.6) the species balance condition does not imply Condition 3.2 for $\theta=(1,1)$; the disjointness of the sign sets is one such hypothesis. Together with the decomposition over strongly connected components (Lemma 3.4), the lemma reduces the verification of Condition 3.2 for all $\theta$ to a smaller family of weight vectors.
--
--   **Formalization Note.** The second paragraph of the printed lemma says "Condition 3.7"; the paper has no Condition 3.7, and the statement refers to the balance equation (3.7), which is what is formalized. The disjunction of the two disjointness conditions is a hypothesis of each part. Maxima are in `WithBot ℝ`, $\gamma_\theta$ is an `EReal` defined by cases without `EReal` subtraction, and $\alpha\ge0$, $\theta^1,\theta^2\ge0$ are the paper's standing assumptions.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 18, Lemma 3.8

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

namespace KangKurtz.Combine

theorem lemma_3_8 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (γ : ℝ) (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (Cond32 ν ν' α β γ θ₁ → Cond32 ν ν' α β γ θ₂ →
      (Disjoint (KangKurtz.SCC.GammaPlus ν ν' θ₁) (KangKurtz.SCC.GammaMinus ν ν' θ₂) ∨
        Disjoint (KangKurtz.SCC.GammaMinus ν ν' θ₁) (KangKurtz.SCC.GammaPlus ν ν' θ₂)) →
      Cond32 ν ν' α β γ (c₁ • θ₁ + c₂ • θ₂)) ∧
    (KangKurtz.SCC.Balance ν ν' α β θ₁ → KangKurtz.SCC.Balance ν ν' α β θ₂ →
      (Disjoint (KangKurtz.SCC.GammaPlus ν ν' θ₁) (KangKurtz.SCC.GammaMinus ν ν' θ₂) ∨
        Disjoint (KangKurtz.SCC.GammaMinus ν ν' θ₁) (KangKurtz.SCC.GammaPlus ν ν' θ₂)) →
      KangKurtz.SCC.Balance ν ν' α β (c₁ • θ₁ + c₂ • θ₂)) := by sorry

end KangKurtz.Combine
