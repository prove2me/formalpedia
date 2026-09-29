-- Prove2me | Theorems.Thm_LiuPass_entropy_ge_of_statDist_le
-- name    : LiuPass.entropy_ge_of_statDist_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T22:26:24.701294+00:00
-- url     : https://prove2.me/theorems/084edb40-34da-483f-834d-5b6eeede6940
-- title:
--   Lemma 2.2: near-uniform implies almost full entropy
-- statement:
--   Lemma 2.2 of the paper. Let $n \ge 4$ and let $X$ be a random variable on $\{0,1\}^n$ whose
--   statistical distance from the uniform distribution satisfies
--   $$\mathrm{SD}(X, U_n) \;\le\; \frac{1}{n^2}.$$
--   Then its Shannon entropy satisfies
--   $$H(X) \;\ge\; n - 2 .$$
--
--   This is the bridge from the statistical closeness that hash-based constructions provide to the
--   Shannon-entropy guarantee required by an entropy-preserving pseudorandom generator. It is used
--   in Theorem 5.5 to show that the output of the construction retains all but $O(\log n)$ bits of
--   entropy. The argument is a counting one: the strings whose probability exceeds $2^{-(n-1)}$
--   contribute at least a quarter of their excess mass to the statistical distance, so they carry
--   total probability at most $4/n^2$, and the remaining mass has surprisal at least $n-1$.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 9, Lemma 2.2

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem entropy_ge_of_statDist_le (n : ℕ) (hn : 4 ≤ n) (p : (Fin n → Bool) → ℝ)
    (hp : IsProbVector p) (hsd : statDist p (unifVector (Fin n → Bool)) ≤ 1 / (n : ℝ) ^ 2) :
    (n : ℝ) - 2 ≤ shannonEntropy p := by sorry
end LiuPass
