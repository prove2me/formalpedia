-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_lemma_7
-- name    : OnlineBudgetAlloc.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:46.266179+00:00
-- url     : https://prove2.me/theorems/040bf8fa-bcbb-4932-ae88-fc8e61d73a96
-- title:
--   Lemma 7 — without the middle phase the bound is exactly $(1 - 1/e)\,\mathrm{OPT}$
-- statement:
--   Let $N > 0$, $H = N/e$, $M = 2N/3$, and let $F$ be the function of display (6).
--
--   **Lemma 7.**
--   $$
--   \frac{11H}{12} + \frac34\int_M^N \Bigl(1 - \frac{H}{x}\Bigr)dx + \int_0^M F(x)\,dx = \Bigl(1 - \frac1e\Bigr)\mathrm{OPT}, \qquad \mathrm{OPT} = \frac{11N}{12}.
--   $$
--
--   If the middle phase were omitted, i.e. if the final phase started with $M$ advertisers instead of $R$, display (7) would give exactly the classical bound $(1 - 1/e)\,\mathrm{OPT}$.
--
--   Differences from the source:
--   - generalization: $N$ the number of advertisers (a positive integer) → every real $N > 0$; reason: the identity is about real numbers only; positive integers are a special case
--   - reading: $\mathrm{OPT}$ → its value $11N/12$; reason: Lemma 2: every input in the support of $D_{N,d}$ has $\mathrm{OPT} = 11N/12$, and the paper substitutes this value itself (proof of Lemma 7)
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.7, Lemma 7, eq. (8)

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Fpot

namespace OnlineBudgetAlloc

/-- **Lemma 7** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.7, eq. (8)). With `H = N/e` and `M = 2N/3`,
`11H/12 + (3/4)∫_M^N (1 − H/x) dx + ∫_0^M F(x) dx = (1 − 1/e)·OPT`, where `OPT = 11N/12`.

**Formalization Note** The identity is stated for every real `N > 0` (the paper's `N` is a positive
integer), and `OPT` is written as its value `11N/12` from Lemma 2, as in the last line of the
proof ("The last equality uses M = 2N/3 and OPT = 11N/12"). -/
theorem lemma_7 (N : ℝ) (hN : 0 < N) :
    11 * (N / Real.exp 1) / 12 +
        3 / 4 * (∫ x in (2 * N / 3)..N, (1 - N / Real.exp 1 / x)) +
        (∫ x in (0 : ℝ)..(2 * N / 3), Fpot (N / Real.exp 1) x) =
      (1 - 1 / Real.exp 1) * (11 * N / 12) := by sorry

end OnlineBudgetAlloc
