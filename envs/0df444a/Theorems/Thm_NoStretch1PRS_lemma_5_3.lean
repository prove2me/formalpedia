-- Prove2me | Theorems.Thm_NoStretch1PRS_lemma_5_3
-- name    : NoStretch1PRS.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:05:29.310334+00:00
-- url     : https://prove2.me/theorems/58c97962-2208-4ad9-84fe-38bcf762630e
-- title:
--   Lemma 5.3 — moments of a chi-squared variable
-- statement:
--   Let $n,r\ge1$, let $X_1,\dots,X_n$ be independent standard normal variables and $Y=\sum_{i=1}^nX_i^2$. Then
--
--   $$\mathbb E[Y^r]=n(n+2)\cdots(n+2r-2)=\prod_{j=0}^{r-1}(n+2j).$$
--
--   Used to compute moments of the block weights of a real Haar vector in Lemma 5.4.
--
--   Differences from the source: none.
-- source:
--   Chen, Coladangelo, Lin, Skoumios, Tysdal, Wang, No linear stretching of single-copy quantum pseudorandomness, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 5.3, p.31 (cited from [JKB94])

import Mathlib

set_option autoImplicit false

namespace NoStretch1PRS

open MeasureTheory

/-- **Lemma 5.3 (moments of a chi-squared variable).**
B. Chen, A. Coladangelo, Y.-T. Lin, N. Skoumios, J. Tysdal, Y. Wang, *No linear stretching of
single-copy quantum pseudorandomness*, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 5.3, p.31 (cited from [JKB94]).

Let `n, r ≥ 1`, `X_1, …, X_n` independent standard normal variables and `Y = ∑_i X_i²`. Then
`E[Y^r] = n(n + 2)⋯(n + 2r − 2)`. -/
theorem lemma_5_3 (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ∫ x, (∑ i, x i ^ 2) ^ r ∂(Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1) =
      ∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j) := by sorry

end NoStretch1PRS
