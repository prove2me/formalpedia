-- Prove2me | Theorems.Thm_GMFGLearn_lemma_7
-- name    : GMFGLearn.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:24.821687+00:00
-- url     : https://prove2.me/theorems/f83b35cf-41bb-46f6-8856-ddff3c8429d5
-- title:
--   Lemma 7 — $\|\mathrm{softmax}_h(x)-\mathrm{argmax\text{-}e}(x)\|_2\le2n\exp(-c'\delta)$ (corrected: $a\ge b$)
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ satisfy $c'(a-b)\le h(a)-h(b)$ for all $a\ge b$. For $x\in\mathbb R^n$ let $x_{\max}=\max_ix_i$ and $\delta=x_{\max}-\max_{x_j<x_{\max}}x_j$, with $\delta:=\infty$ when all $x_j$ are equal. Then
--
--   $$
--   \|\mathrm{softmax}_h(x)-\mathrm{argmax\text{-}e}(x)\|_2\le2n\exp(-c'\delta);
--   $$
--
--   when all $x_j$ are equal, $\mathrm{softmax}_h(x)=\mathrm{argmax\text{-}e}(x)$.
--
--   This is Condition 2 of $\mathcal F_{c,c'}$ for the generalized softmax operators: with an action gap, the smoothed policy is exponentially close to the greedy one.
--
--   Differences from the source:
--   - correction: c′(a − b) ≤ h(a) − h(b) for any a ≤ b → for any a ≥ b; reason: with a ≤ b, h ≡ 0 qualifies and n = 2, c′ = 10, x = (1,0) give ‖(1/2,1/2) − (1,0)‖₂ ≈ 0.707 > 4e^{−10}; the proof uses h(x⋆) − h(x_i) ≥ c′δ_i with x⋆ > x_i, as in (21)
--   - generalization: δ := ∞ when all x_j are equal, bound 2n exp(−c′δ) → the equality softmax_h(x) = argmax-e(x), for every c′; reason: for c′ > 0 the printed bound is 0, i.e. this equality; for c′ ≤ 0 the printed right side is not finite and the equality is stronger
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, Lemma 7, p.21

import Mathlib
import Definitions.Def_GMFGLearn_Smoothing

namespace GMFGLearn

/-- **Lemma 7 (`softmax_h` is close to argmax-e).** Guo–Hu–Xu–Zhang, *A General Framework for
Learning Mean-Field Games*, arXiv:2003.06069v3, Lemma 7, p.21: "Suppose that h : ℝ → ℝ satisfies
c′(a − b) ≤ h(a) − h(b) for any a ≤ b ∈ ℝ. Then for any x ∈ ℝ^n, … ‖softmax_h(x) − argmax-e(x)‖2 ≤
2n exp(−c′δ), where δ = x_max − max_{x_j<x_max} x_j, x_max = max_{i=1,...,n} x_i, and δ := ∞ when
all x_j are equal."

**Formalization Note** Corrected hypothesis: `a ≥ b` instead of the printed `a ≤ b`. The proof uses
`h(x⋆) − h(x_i) ≥ c′δ_i` with `x⋆ > x_i`, i.e. `a ≥ b`, as in (21). With `a ≤ b`, `h ≡ 0` qualifies
and `n = 2`, `c′ = 10`, `x = (1,0)` give `‖(1/2,1/2) − (1,0)‖₂ ≈ 0.707 > 4e^{−10}`. The case `δ = ∞`
(all entries equal) is stated as the exact equality `softmax_h(x) = argmax-e(x)`. -/
theorem lemma_7 (n : ℕ) (c' : ℝ) (h : ℝ → ℝ)
    (hh : ∀ a b : ℝ, b ≤ a → c' * (a - b) ≤ h a - h b) (x : Fin n → ℝ) :
    (AllEqual x → softmaxH h x = argmaxE x) ∧
      (¬ AllEqual x →
        l2 (softmaxH h x - argmaxE x) ≤ 2 * (n : ℝ) * Real.exp (-(c' * gap x))) := by sorry

end GMFGLearn
