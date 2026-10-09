-- Prove2me | Theorems.Thm_KangKurtz_SecondScale_gammaTheta_ge
-- name    : KangKurtz.SecondScale.gammaTheta_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:20.552785+00:00
-- url     : https://prove2.me/theorems/19f639f0-6add-476c-9fe9-571a0c26c2f6
-- title:
--   §4, p. 21 — a combination cannot change faster than its fastest supported species
-- statement:
--   Let $\theta$ be a nonnegative vector of weights on the species of a finite reaction network. Write $\gamma_i$ for the natural time scale of species $i$, $\gamma_\theta$ for the natural time scale of the weighted combination, and $r_1=\min_i\gamma_i$. Then
--
--   $$\gamma_\theta\geq\min_{i:\theta_i>0}\gamma_i,\qquad r_1=\inf_{\eta\geq0}\gamma_\eta.$$
--
--   This identifies the first time scale from the time scales of all nonnegative combinations and is the lower-bound step used in Lemma 4.4.
--
--   **Formalization Note** An empty minimum is $+\infty$. A combination unchanged by every reaction also has time scale $+\infty$. The infimum equals the paper's minimum because a coordinate vector realizes each species time scale.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 21, §4, first sentence

import Mathlib
import Definitions.Def_KangKurtz_SecondScale_Setting

namespace KangKurtz.SecondScale

theorem gammaTheta_ge {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i) (β : Fin r → ℝ)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i) :
    (⨅ i ∈ support θ, gammaSp ν ν' α β i) ≤ KangKurtz.SCC.gammaTheta ν ν' α β θ ∧
    r1 ν ν' α β =
      ⨅ η ∈ {η : Fin s → ℝ | ∀ i, 0 ≤ η i}, KangKurtz.SCC.gammaTheta ν ν' α β η := by sorry

end KangKurtz.SecondScale
