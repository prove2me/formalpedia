-- Prove2me | Theorems.Thm_Hoeffding_card_filter_sign_sum_le
-- name    : Hoeffding.card_filter_sign_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:41.399576+00:00
-- url     : https://prove2.me/theorems/87d192cc-bfff-40ea-9b36-fa790971fa9d
-- title:
--   Hoeffding’s bound in counting form for Rademacher sign patterns
-- statement:
--   **Hoeffding's inequality in counting form.** Let $l \ge 1$, let
--   $c_1, \dots, c_l \in \mathbb{R}$ satisfy $|c_i| \le 1$, and let $t \ge 0$. For a sign pattern
--   $\sigma \in \{-1, +1\}^{l}$ write $\langle \sigma, c\rangle = \sum_{i=1}^{l} \sigma_i c_i$. Then
--   the number of sign patterns whose signed sum reaches $t$ satisfies
--
--   $$
--   \#\bigl\{\, \sigma \in \{-1,+1\}^{l} \;:\; \langle \sigma, c\rangle \ge t \,\bigr\}
--   \;\le\; 2^{l}\, \exp\!\Bigl(-\frac{t^{2}}{2l}\Bigr).
--   $$
--
--   Dividing by $2^l$ recovers the probabilistic statement for independent uniform signs, but the
--   counting form is the one needed in practice: a symmetrization argument fixes the sample and
--   averages over sign patterns, so the quantity to be bounded is a cardinality of a finite set, not
--   a probability on an abstract space. This is the step that produces the exponential factor in
--   Vapnik–Chervonenkis bounds and in Rademacher complexity estimates.
--
--   **Formalization Note** Sign patterns are `Fin l → Bool` with `true` read as $+1$, and the
--   cardinality is that of a `Finset.filter` over `Finset.univ`, cast to $\mathbb{R}$.
-- source:
--   W. Hoeffding, Probability inequalities for sums of bounded random variables, J. Amer. Statist. Assoc. 58 (1963), 13–30, Theorem 2; counting form as used in symmetrization arguments. Carved from the accepted proof of BartlettNN.Sigmoid.theorem28_part1, https://prove2.me/submissions/0f39c22d-cf6c-4cef-9f8e-35718ff87eba

import Mathlib

set_option autoImplicit false
open Finset

theorem Hoeffding.card_filter_sign_sum_le {l : ℕ} (hl : 1 ≤ l) (c : Fin l → ℝ) (hc : ∀ i, |c i| ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ)
      ≤ (2 : ℝ) ^ l * Real.exp (-(t ^ 2 / (2 * l))) := by sorry
