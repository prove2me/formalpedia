-- Prove2me | Theorems.Thm_LefebvreVariations_vc_gamma_estimate_le_twenty
-- name    : LefebvreVariations.vc_gamma_estimate_le_twenty
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:32.130059+00:00
-- url     : https://prove2.me/theorems/2206ecad-5731-5780-bbd9-a82afbacfacf
-- title:
--   Lefebvre's variations, No. 195 — on a theme by Vapnik and Chervonenkis: the Vapnik–Chervonenkis Γ estimate for double samples of size at most 40
-- statement:
--   Let $l$ and $m$ be integers with $1\le l\le 20$ and $0\le m\le 2l$, and let $\varepsilon>0$ be real. Then
--   $$
--   \frac{1}{\binom{2l}{l}}\sum_{\substack{0\le k\le l\\ |2k-m|/l\ \ge\ \varepsilon/2}}\binom{m}{k}\binom{2l-m}{l-k}\ \le\ 2\,e^{-\varepsilon^{2}l/8}.
--   $$
--
--   In the proof of the Vapnik–Chervonenkis inequality for uniform convergence of relative frequencies, a double sample of size $2l$ contains $m$ marked terms, and $k$ of them fall in the first half-sample; the left-hand side is the probability, under a uniformly random split, that the two half-samples' marked fractions $k/l$ and $(m-k)/l$ differ by at least $\varepsilon/2$. The estimate is stated in the original paper without proof; the platform lists it as open for all $l$.
--
--   **Formalization Note** The summation runs over `k ∈ Finset.range (l + 1)` with the filter `ε / 2 ≤ |(2 * k - m) / l|` computed in `ℝ`. The binomial `(2 * l - m).choose (l - k)` uses natural subtraction, which is harmless since `m ≤ 2 * l` and terms with `k > m` or `l - k > 2 * l - m` vanish (their binomial is zero); for `k > l` there is no term. The only change from the platform statement is the added hypothesis `l ≤ 20`.
--
--   **Why this is a variation.** A variation on the open platform problem VapnikChervonenkis.Inequality.gamma_estimate (the Gamma estimate, stated without proof in the 1971 paper), played at l <= 20 with the parent's formula copied verbatim. The statement for all l remains open on the platform; the numerical check goes to l = 60 with worst ratio 0.824.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   V. N. Vapnik and A. Ya. Chervonenkis, On the uniform convergence of relative frequencies of events to their probabilities, Theory of Probability and its Applications 16 (1971), 264-280; the estimate of Gamma is stated there without proof (page and wording as recorded by the platform, not re-checked). Checked numerically in exact binomial arithmetic for all l <= 60, all 0 <= m <= 2l, at every value of epsilon where the summation set changes (the left side is a step function and the right side decreases, so these are the worst cases): the largest ratio of left to right side is 0.824, at l = 1, m = 1, epsilon = 2.

import Mathlib

namespace LefebvreVariations

/-- The Vapnik–Chervonenkis `Γ` estimate (the hypergeometric tail of a double sample) at its
first sizes `l ≤ 20`: for a double sample of size `2l` of which `m` terms lie in `A`, with `k` the
number of marked terms in the first semi-sample,
`Σ_{k : |2k/l − m/l| ≥ ε/2} C(m,k) C(2l−m, l−k) / C(2l, l) ≤ 2 e^{−ε² l / 8}`.
Source: V. N. Vapnik and A. Ya. Chervonenkis, *On the uniform convergence of relative frequencies
of events to their probabilities*, Theory Probab. Appl. 16 (1971) (the bound is stated there
without proof; cited from memory). A direct computation over `l ≤ 60`, all `m`, at every threshold
value of `ε` gives a worst ratio of left side to right side of about `0.82`. -/
theorem vc_gamma_estimate_le_twenty (l m : ℕ) (ε : ℝ) (hl : 1 ≤ l) (hl20 : l ≤ 20)
    (hm : m ≤ 2 * l) (hε : 0 < ε) :
    (∑ k ∈ (Finset.range (l + 1)).filter (fun k : ℕ => ε / 2 ≤ |(2 * (k : ℝ) - (m : ℝ)) / (l : ℝ)|),
        ((m.choose k * (2 * l - m).choose (l - k) : ℕ) : ℝ)) / ((2 * l).choose l : ℝ)
      ≤ 2 * Real.exp (-(ε ^ 2 * l / 8)) := by
  sorry

end LefebvreVariations
