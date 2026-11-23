-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2_correctness_transfer
-- name    : ITPIRPreproc.MatchVec.lemma_4_2_correctness_transfer
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:47:58.768061+00:00
-- url     : https://prove2.me/theorems/34a50ece-d973-4385-b512-5e2490afff08
-- title:
--   Per-round adaptive correctness from independent pool-failure models
-- statement:
--   Suppose every positive-probability query prefix of $S$ has an independent-pool failure model. Then every individual adaptive retrieval has failure probability at most $(7/8)^s$.
--
--   Within one model, monotonicity and independence give
--   $$
--   \mu(\mathrm{failure})
--    \le \mu\bigl(\bigcap_{\ell<s}B_\ell\bigr)
--    =\prod_{\ell<s}\mu(B_\ell)
--    \le (7/8)^s.
--   $$
--   Thus the measure of the part of the actual round-failure event in a prefix $qs$ is at most $\Pr[H_j=qs](7/8)^s$. On a zero-probability prefix the corresponding joint event also has measure zero. Finally, sum over the countable type `List (List Bool)` of query prefixes. The prefixes are pairwise disjoint and measurable and have total probability at most one, so the unconditional round-failure measure is at most $(7/8)^s$. This is precisely `PerRoundCorrect`.
--
--   No independence between different retrieval rounds is assumed: every model is conditional on the complete previous query prefix, and the adversary may choose its next index adaptively.
-- source:
--   Dujmovic--Lai--Wichs, STOC 2027 submission #572, §4.2 correctness argument, printed pp.14--15 (PDF pp.16--17). For an uncached target there are $s=8(\lambda+1)$ independent attempts and each succeeds with probability at least $1/8$; soundness rules out wrong returned bits. The countable-prefix summation formalizes conditioning on the adversary's history.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerRoundModels

open MeasureTheory
open scoped ENNReal

open ITPIRPreproc.MatchVec

theorem ITPIRPreproc.MatchVec.lemma_4_2_correctness_transfer (S : Scheme) (n lam s : ℕ)
    (h : FailureModeled S n lam s) :
    PerRoundCorrect S n lam ((7 / 8 : ℝ≥0∞) ^ s) := by sorry
