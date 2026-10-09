-- Prove2me | Theorems.Thm_KangKurtz_SecondScale_lemma_4_4_alpha
-- name    : KangKurtz.SecondScale.lemma_4_4_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:06.719545+00:00
-- url     : https://prove2.me/theorems/58e81afa-22b5-4713-b695-113ed2fd6f5d
-- title:
--   Lemma 4.4, p. 21 — a changing fast reaction forces a larger abundance exponent
-- statement:
--   Let $\theta\in\mathbb K_2$, let $l\in\Gamma_i^{r_1}$, and suppose the weighted combination changes under reaction $l$, meaning $\theta\cdot\zeta_l\ne0$. Then
--
--   $$\alpha_\theta>\alpha_i.$$
--
--   This is the first assertion of Lemma 4.4 and excludes equality of the second time scale with the first when a first-scale reaction changes the combination.
--
--   **Formalization Note** The nonzero dot product forces $\theta$ to have a positive coordinate, so $\alpha_\theta$ is a genuine maximum. Membership in $\mathbb K_2$ includes both nonnegativity and the projected orthogonality equations.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 21, Lemma 4.4, first sentence

import Mathlib
import Definitions.Def_KangKurtz_SecondScale_Setting

namespace KangKurtz.SecondScale

theorem lemma_4_4_alpha {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i) (β : Fin r → ℝ)
    (θ : Fin s → ℝ) (i : Fin s) (l : Fin r)
    (hθ : θ ∈ K2 ν ν' α β) (hl : l ∈ GammaR1 ν ν' α β i)
    (hdot : KangKurtz.SCC.dot ν ν' θ l ≠ 0) :
    α i < alphaTheta α θ := by sorry

end KangKurtz.SecondScale
