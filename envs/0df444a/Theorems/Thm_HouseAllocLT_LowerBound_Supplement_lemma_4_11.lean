-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_11
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:21:54.087861+00:00
-- url     : https://prove2.me/theorems/fe29299a-8ccb-490b-bd07-f6f99f2206d3
-- title:
--   Lemma 4.11 — RPG weakly and RES strictly favour truth at the first changed class
-- statement:
--   Let $n,m\ge1$ and fix a routine. Fix the other agents' reports, agent $i$'s true list $P_i$ and another report $R_i$, and write $\Phi_{i,j}^{P_i}$ for the probability that $i$ receives an object of its true class $j$.
--
--   1. Let $k$ be the first class where $R_i$ and $P_i$ differ and suppose the true class $S=C_k^i$ is nonempty. Under RPG, $\Phi^{P_i}_{i,j}(P_i,P_{-i})=\Phi^{P_i}_{i,j}(R_i,P_{-i})$ for every $j<k$ and $\Phi^{P_i}_{i,k}(P_i,P_{-i})\ge\Phi^{P_i}_{i,k}(R_i,P_{-i})$. Under RES the same equalities hold below $k$ and
--   $$\Phi^{P_i}_{i,k}(P_i,P_{-i})>\Phi^{P_i}_{i,k}(R_i,P_{-i}).$$
--   2. If $R_i$ only adds classes after the end of $P_i$, then under RPG and under RES every true-rank probability is unchanged.
--
--   Together these give the LT clause of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
--   - encoding: "the first class where the two lists differ" → an index k with equal classes below k and different classes at k; reason: these conditions characterize the first differing class
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.11, PDF p. 13 (printed p. 11); RES from display (14); proof PDF p. 21 (printed p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_LTRPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.11, PDF p. 13 (printed p. 11). Fix the other agents' reports, agent `i`'s true list
`P i` and another report `R`. Let `k` be the first class where the two lists differ, with true
class `S = C_k^i` nonempty. Under RPG the true-rank probabilities below `k` are equal and the
truthful one at `k` is at least as large; under RES the earlier ones are equal and the truthful
one at `k` is strictly larger. If `R` only adds classes after the true list ends, both
mechanisms leave every true-rank probability unchanged. -/
theorem lemma_4_11 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m)
    (P : Profile n m) (i : Fin n) (R : Preference m) :
    (∀ k : ℕ, (∀ j < k, R.classes j = (P i).classes j) → R.classes k ≠ (P i).classes k →
      ((P i).classes k).Nonempty →
      ((∀ j < k, trueClassProb (rpg MM) i (P i) P j =
          trueClassProb (rpg MM) i (P i) (Function.update P i R) j) ∧
        trueClassProb (rpg MM) i (P i) (Function.update P i R) k ≤
          trueClassProb (rpg MM) i (P i) P k) ∧
      ((∀ j < k, trueClassProb res i (P i) P j =
          trueClassProb res i (P i) (Function.update P i R) j) ∧
        trueClassProb res i (P i) (Function.update P i R) k <
          trueClassProb res i (P i) P k)) ∧
    ((P i).length ≤ R.length → (∀ j < (P i).length, R.classes j = (P i).classes j) →
      ∀ j : ℕ,
        trueClassProb (rpg MM) i (P i) (Function.update P i R) j =
          trueClassProb (rpg MM) i (P i) P j ∧
        trueClassProb res i (P i) (Function.update P i R) j =
          trueClassProb res i (P i) P j) := by sorry

end HouseAllocLT.LowerBound.Supplement
