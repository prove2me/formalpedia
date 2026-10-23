-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_lemma_A_4
-- name    : LargeDelaySGD.MeanSquare.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:24:06.172423+00:00
-- url     : https://prove2.me/theorems/06c690a6-5ba0-479c-a888-b83eea70cbbc
-- title:
--   Lemma A.4, p. 22 — a_n, b_n ≥ 0, Σ a_n = ∞, Σ a_n b_n < ∞ and |b_{n+1} − b_n| ≤ K a_n imply b_n → 0
-- statement:
--   Let $(a_n)$ and $(b_n)$ be nonnegative real sequences with
--
--   $$\sum_n a_n=\infty,\qquad\sum_n a_nb_n<\infty,$$
--
--   and suppose there is a real $K>0$ with $|b_{n+1}-b_n|\le K a_n$ for every $n$. Then $\lim_{n\to\infty}b_n=0$.
--
--   This elementary series lemma is the bridge from Lemmas 1 and 2 to Theorem 1, applied with $a_n=\alpha_{n+1}$ and $b_n=\mathbb E\|\nabla f(X_n)\|_2^2$.
--
--   **Formalization Note.** The paper indexes the sums from $n=1$, the Lean statement from $n=0$; a finite prefix changes neither condition. "$=\infty$" is `¬ Summable` and "$<\infty$" is `Summable`, which is exact for nonnegative series.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, App. A, p. 22, Lemma A.4

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem lemma_A_4 (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hsa : ¬ Summable a) (hsab : Summable (fun n => a n * b n))
    (K : ℝ) (hK : 0 < K) (hinc : ∀ n, |b (n + 1) - b n| ≤ K * a n) :
    Filter.Tendsto b Filter.atTop (nhds 0) := by sorry

end LargeDelaySGD.MeanSquare
