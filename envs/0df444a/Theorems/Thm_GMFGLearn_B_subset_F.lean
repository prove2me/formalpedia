-- Prove2me | Theorems.Thm_GMFGLearn_B_subset_F
-- name    : GMFGLearn.B_subset_F
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:21.376531+00:00
-- url     : https://prove2.me/theorems/6e1d6fd2-b215-4222-8c4c-d60a4ae85cb4
-- title:
--   §4.2 — $\mathcal B_{c,c'}\subseteq\mathcal F_{c,c'}$
-- statement:
--   For positive constants $c,c'>0$, every generalized softmax operator $\mathrm{softmax}_h:\mathbb R^n\to\mathbb R^n$ whose $h$ satisfies $c'(x-y)\le h(x)-h(y)\le c(x-y)$ for all $x\ge y$ belongs to $\mathcal F_{c,c'}$: it is $c$-Lipschitz in $\|\cdot\|_2$ (Condition 1) and satisfies $\|\mathrm{softmax}_h(x)-\mathrm{argmax\text{-}e}(x)\|_2\le2n\exp(-c'\delta)$ (Condition 2). In short,
--
--   $$
--   \mathcal B_{c,c'}\subseteq\mathcal F_{c,c'} .
--   $$
--
--   In particular $\mathcal F_{c,c}$ contains the classical softmax with temperature $c$, so the smoothing hypothesis of Theorem 2 can be met.
--
--   Differences from the source:
--   - encoding: Condition 2 with δ := ∞ when all x_j are equal → f(x) = argmax-e(x) when all x_j are equal; reason: 2n exp(−c′·∞) = 0 for c′ > 0, and c′ > 0 here
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, §4.2, p.12 (B_{c,c'} and (21)); Conditions 1–2, p.11

import Mathlib
import Definitions.Def_GMFGLearn_Smoothing

namespace GMFGLearn

/-- **`B_{c,c′} ⊆ F_{c,c′}`.** Guo–Hu–Xu–Zhang, *A General Framework for Learning Mean-Field Games*,
arXiv:2003.06069v3, §4.2, p.12: "This operator is Lipschitz continuous and close to the argmax-e
(see Lemmas 6 and 7 in the Appendix), and in particular one can show that B_{c,c′} ⊆ F_{c,c′}."

**Formalization Note** For positive constants `c, c′ > 0` (p.11), on `ℝⁿ = Fin n → ℝ`. -/
theorem B_subset_F (n : ℕ) (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') :
    (BSet c c' : Set ((Fin n → ℝ) → Fin n → ℝ)) ⊆ FSet c c' := by sorry

end GMFGLearn
