-- Prove2me | Theorems.Thm_KangKurtz_SecondScale_lemma_4_4
-- name    : KangKurtz.SecondScale.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:14.182005+00:00
-- url     : https://prove2.me/theorems/45de719b-bd9a-4460-ba9c-d5cf84069bf4
-- title:
--   Lemma 4.4, p. 21 — the second time scale exceeds the first
-- statement:
--   For a finite reaction network, let $r_1=\min_i\gamma_i$ be the first natural time scale. Let $\mathbb K_2$ consist of the nonnegative weighted combinations unchanged by the projected first-scale reactions, and set $r_2=\inf_{\theta\in\mathbb K_2}\gamma_\theta$. If at least one reaction changes at least one species, then
--
--   $$r_2>r_1.$$
--
--   This separates the first and second natural time scales defined in Section 4.
--
--   **Formalization Note** The requirement that some $\zeta_{ik}\ne0$ makes $r_1$ finite. It is a necessary explicit addition: if every reaction has zero net change, both time scales are $+\infty$ and the strict inequality is false. The infimum is over all of $\mathbb K_2$, including combinations unchanged by every reaction.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 21, Lemma 4.4, second part

import Mathlib
import Definitions.Def_KangKurtz_SecondScale_Setting

namespace KangKurtz.SecondScale

theorem lemma_4_4 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i) (β : Fin r → ℝ)
    (hζ : ∃ k i, ν' k i ≠ ν k i) :
    r1 ν ν' α β < r2 ν ν' α β := by sorry

end KangKurtz.SecondScale
