-- Prove2me | Theorems.Thm_MultiStageAlloc_Supplement_theorem_3
-- name    : MultiStageAlloc.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:23:05.460773+00:00
-- url     : https://prove2.me/theorems/30a611c6-3e72-4ea2-b6f5-b900e4add9ea
-- title:
--   Theorem 3 (Tight Upper-bound for Multi-stage Matching) — no algorithm beats $\Gamma(K)$
-- statement:
--   For every number of stages $K\ge1$ and every multi-stage fractional matching algorithm $\mathcal A$ with $K$ stages, deterministic or randomized, there is an instance $I$ of the $K$-stage unweighted matching problem with
--
--   1. all weights $w_j=1$ and all capacities $n_j=1$,
--   2. every batch $U_1,\dots,U_K$ nonempty,
--   3. $\mathrm{OPT}(I)>0$,
--
--   on which the expected total weight of $\mathcal A$ satisfies
--   $$
--   \mathbb E\bigl[\mathrm{ALG}(I)\bigr]\ \le\ \Gamma(K)\cdot\mathrm{OPT}(I),\qquad \Gamma(K)=1-\Bigl(1-\frac1K\Bigr)^{K}.
--   $$
--
--   Here $\mathrm{OPT}(I)$ is the optimal value of the fractional offline matching LP. Consequently no multi-stage fractional matching algorithm is $\alpha$-competitive for any $\alpha>\Gamma(K)$, so the ratio of Theorem 1 is optimal. The same holds for integral algorithms, which are a special case.
--
--   **Formalization Note** A randomized algorithm is a probability measure over deterministic non-anticipating algorithms, and its value on $I$ is the expectation in Definition 1. The algorithm is a single rule defined on all finite instances, each with $n$ online and $m$ offline vertices for some $n,m$.
--
--   Differences from the source:
--   - reading: “no multi-stage fractional matching algorithm can achieve a competitive ratio better than Γ(K)” → every randomized algorithm has an unweighted instance with nonempty batches and OPT(I) > 0 on which E[ALG(I)] ≤ Γ(K)·OPT(I); reason: the existence of such an instance is exactly inf_I ALG(I)/OPT(I) ≤ Γ(K); OPT(I) > 0 makes the ratio defined, and the paper's proof covers “any given (possibly randomized)” algorithm
--   - generalization: an algorithm that sees batch k and its edges at stage k → a non-anticipating algorithm that may in addition read the numbers n and m of vertices; reason: a larger class of algorithms makes the impossibility stronger; every algorithm of the paper's class is in it
--   - encoding: algorithms defined on instances with |U_k| ≥ 1 (§2.1) → algorithms defined on every instance of the base model, where batches may be empty; reason: every algorithm on the paper's class extends: at stage s copy its allocation on any instance with nonempty batches that agrees through stage s, and allocate 0 if there is none; the witness instance has every batch nonempty
--   - encoding: a randomized algorithm → a probability measure over deterministic non-anticipating algorithms with measurable value; reason: fixing the random bits in advance turns a randomized algorithm into such a mixture; a Dirac measure is a deterministic algorithm
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Theorem 3, p.30 (proof §5.1, pp.31–32)

import Mathlib
import Definitions.Def_MultiStageAlloc_OfflineLP
import Definitions.Def_MultiStageAlloc_Supplement_MatchingAlgorithm

namespace MultiStageAlloc.Supplement

/-- **Theorem 3 (Tight Upper-bound for Multi-stage Matching).** Feng & Niazadeh, *Batching and
Optimal Multi-stage Bipartite Allocations*, arXiv:2211.16581v1, p.30. No multi-stage fractional
matching algorithm can achieve a competitive ratio better than `Γ(K) = 1 - (1 - 1/K)^K` in the
`K`-stage (unweighted) matching problem: for every `K ≥ 1` and every (possibly randomized)
`K`-stage fractional matching algorithm, there is an unweighted instance (all weights and
capacities `1`) with every batch nonempty and `OPT(I) > 0` on which the algorithm's expected total
weight is at most `Γ(K) · OPT(I)`. Hence no such algorithm is `α`-competitive for any `α > Γ(K)`.

**Formalization Note.** `OPT` is the fractional offline LP value of the base mission. A randomized
algorithm is a probability measure over deterministic non-anticipating algorithms (`RandomizedAlgorithm`);
a Dirac measure gives the deterministic case, and integral algorithms are a special case of fractional
ones. The witness has `OPT(I) > 0`, so the ratio of Definition 1 is defined on it. -/
theorem theorem_3 (K : ℕ) (hK : 1 ≤ K) {Ω : Type*} [MeasurableSpace Ω]
    (R : RandomizedAlgorithm K Ω) :
    ∃ (n m : ℕ) (I : Instance (Fin n) (Fin m) K),
      (∀ j, I.w j = 1) ∧ (∀ j, I.cap j = 1) ∧
      (∀ k ∈ Finset.Icc 1 K, ∃ i, I.batch i = k) ∧
      0 < OPT I ∧ expectedALG R I ≤ gammaK K * OPT I := by sorry

end MultiStageAlloc.Supplement
