-- Prove2me | Theorems.Thm_OnlineCRS_Combine_chi_fkg
-- name    : OnlineCRS.Combine.chi_fkg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:28.410955+00:00
-- url     : https://prove2.me/theorems/391c1160-a1fb-437a-bd0e-b441c02e6f4d
-- title:
--   Proof of Lemma 2.11, p. 16 — FKG correlation of selectability events
-- statement:
--   Let $x\in[0,1]^N$, let $R(x)$ contain each element independently with probability $x_e$, and fix families $F_1,F_2$. Writing $H=F_1\cap F_2$, the two events $\chi_e(R(x),F_1,H)$ and $\chi_e(R(x),F_2,H)$ satisfy
--
--   $$
--   \Pr[\chi_e(R(x),F_1,H)]\,\Pr[\chi_e(R(x),F_2,H)]
--   \leq \Pr[\chi_e(R(x),H,H)].
--   $$
--
--   This is the fixed-family FKG step in Lemma 2.11. It is reusable for intersections of other downward events under independent activation.
--
--   **Formalization Note** The coordinate bounds keep the product weights nonnegative and summing to one.
-- source:
--   arXiv:1508.00142v2, §2.4, proof of Lemma 2.11, p. 16, FKG display

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Combination

namespace OnlineCRS.Combine

/-- The FKG correlation step in the proof of Lemma 2.11, p. 16. -/
theorem chi_fkg {α : Type} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (e : α) (F₁ F₂ : Finset (Finset α))
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1) :
    chiProb x e F₁ (F₁ ∩ F₂) * chiProb x e F₂ (F₁ ∩ F₂) ≤
      chiProb x e (F₁ ∩ F₂) (F₁ ∩ F₂) := by sorry

end OnlineCRS.Combine
