-- Prove2me | Theorems.Thm_GMFGLearn_lemma_6
-- name    : GMFGLearn.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:33.151993+00:00
-- url     : https://prove2.me/theorems/c44ff29e-c78c-4ebc-8610-98fe42434a78
-- title:
--   Lemma 6 — $\mathrm{softmax}_h$ is $c$-Lipschitz (corrected: two-sided Lipschitz condition on $h$)
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be $c$-Lipschitz, i.e. $|h(a)-h(b)|\le c(a-b)$ for all $a\ge b$. Then for all $x,y\in\mathbb R^n$,
--
--   $$
--   \|\mathrm{softmax}_h(x)-\mathrm{softmax}_h(y)\|_2\le c\,\|x-y\|_2 .
--   $$
--
--   This is Condition 1 of $\mathcal F_{c,c'}$ for the generalized softmax operators.
--
--   Differences from the source:
--   - correction: h(a) − h(b) ≤ c(a − b) for a ≥ b → |h(a) − h(b)| ≤ c(a − b) for a ≥ b; reason: the printed one-sided hypothesis allows a steeply decreasing h: n = 2, c = 1, h(t) = −100t, x = (0,0), y = (0.01,0) give ‖softmax_h(x) − softmax_h(y)‖₂ ≈ 0.327 > 0.01; the proof uses that h̃ is c-Lipschitz, and every h of B_{c,c′} satisfies it
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, Lemma 6, p.21

import Mathlib
import Definitions.Def_GMFGLearn_Smoothing

namespace GMFGLearn

/-- **Lemma 6 (`softmax_h` is `c`-Lipschitz).** Guo–Hu–Xu–Zhang, *A General Framework for Learning
Mean-Field Games*, arXiv:2003.06069v3, Lemma 6, p.21: "Suppose that h : ℝ → ℝ satisfies
h(a) − h(b) ≤ c(a − b) for any a ≥ b ∈ ℝ. Then the softmax function softmax_h is c-Lipschitz,
i.e., ‖softmax_h(x) − softmax_h(y)‖2 ≤ c‖x − y‖2 for any x, y ∈ ℝ^n."

**Formalization Note** Corrected hypothesis: `h` is `c`-Lipschitz, `|h(a) − h(b)| ≤ c(a − b)` for
`a ≥ b`, which is what the proof uses ("h̃ is c-Lipschitz continuous"). The printed one-sided
hypothesis allows a steeply decreasing `h`: `n = 2`, `c = 1`, `h(t) = −100t`, `x = (0,0)`,
`y = (0.01,0)` give `‖softmax_h(x) − softmax_h(y)‖₂ ≈ 0.327 > 0.01 = c‖x − y‖₂`. `ℝⁿ` is
`Fin n → ℝ` with the Euclidean norm `l2`. -/
theorem lemma_6 (n : ℕ) (c : ℝ) (h : ℝ → ℝ)
    (hh : ∀ a b : ℝ, b ≤ a → h a - h b ≤ c * (a - b) ∧ h b - h a ≤ c * (a - b))
    (x y : Fin n → ℝ) :
    l2 (softmaxH h x - softmaxH h y) ≤ c * l2 (x - y) := by sorry

end GMFGLearn
