-- Prove2me | Theorems.Thm_LefebvreVariations_shapiro_le_twelve
-- name    : LefebvreVariations.shapiro_le_twelve
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:19:11.837799+00:00
-- url     : https://prove2.me/theorems/f2245d68-b991-420b-8b85-da6022676fca
-- title:
--   Lefebvre's variations, No. 189 — on a theme by Shapiro: the Shapiro harmonic criterion holds for n at most twelve
-- statement:
--   For $n\ge1$ let $\delta_n=\prod_{j=1}^{n-1}\operatorname{lcm}(1,2,\dots,j)$. For every integer $1\le n\le 12$,
--   $$
--   \Bigl(H_{\delta_n}-\frac{n^2}{2}\Bigr)^2\ <\ 36\,n^3 ,
--   $$
--   where $H_m=\sum_{k\le m}1/k$.
--
--   The parent asserts this for all $n\ge1$, as an equivalent of the Riemann hypothesis. Since $\log\delta_n=\sum_{j<n}\psi(j)\approx n^2/2$, the left side is of the order of a squared prime-number-theorem error term. For $n\le 12$, $\delta_{12}$ is an integer of about 30 digits.
--
--   **Formalization Note** The statement is that of `BroughanRH.shapiro` verbatim (the `let δ`, `harmonic` cast from $\mathbb{Q}$ to $\mathbb{R}$), with the added hypothesis `n ≤ 12`. For $n=1$, $\delta_1=1$ (empty product) and the left side is $1/4$.
--
--   **Why this is a variation.** Variation on the open platform theorem BroughanRH.shapiro (an equivalent of the Riemann hypothesis): the parent's own inequality for n <= 12, where delta_n is an explicit integer and the claim is a finite computation with harmonic numbers.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Statement and name as on the platform (BroughanRH.shapiro, from K. Broughan, Equivalents of the Riemann Hypothesis, Cambridge Univ. Press, 2017; the exact reference is cited from memory and was not confirmed by web search). Truth check: computed exactly in Python with mpmath (40 digits): the left side for n = 1..12 is 0.25, 1, 9, 23.98, 48.30, 69.87, 115.87, 149.43, 195.74, 245.19, 335.86, 384.03, against 36 n^3 = 36, 288, 972, 2304, ..., 62208; also true for n = 20, 30, 40.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem shapiro_le_twelve :
    let δ (n : ℕ) : ℕ := ∏ j ∈ Finset.Ico 1 n, (Finset.Icc 1 j).lcm id
    ∀ n : ℕ, 1 ≤ n → n ≤ 12 → ((harmonic (δ n) : ℝ) - (n : ℝ)^2/2)^2 < 36*(n : ℝ)^3 := by
  sorry

end LefebvreVariations
