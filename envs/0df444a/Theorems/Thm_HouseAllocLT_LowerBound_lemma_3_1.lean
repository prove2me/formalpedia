-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_lemma_3_1
-- name    : HouseAllocLT.LowerBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:08.881284+00:00
-- url     : https://prove2.me/theorems/095d7abe-f8fe-4ff7-a892-0140ec35f3b1
-- title:
--   Lemma 3.1 — common-prefix probabilities are unchanged
-- statement:
--   Let $n\ge1$, and let $\phi$ be feasible and LT on $D_n^n$. Fix an agent $i$, the other agents' reports in $D_n$, and an object $a_j$. For any two lengths $q,q'\in\{j,\ldots,n\}$,
--
--   $$\phi_{i,a_j}(P^q,P_{-i})=\phi_{i,a_j}(P^{q'},P_{-i}).$$
--
--   This invariance identifies the assignment marginals shared by reports with a common prefix. No truthfulness outside $D_n^n$ is assumed.
--
--   Differences from the source:
--   - encoding: agents, objects and ranks numbered from one → Fin indices numbered from zero; reason: the bijection sends each code index j to the source index j+1
--   - encoding: lottery on feasible matchings → real probability vector on finite edge sets with feasible support; reason: these encode exactly the same distributions, including irrational weights
--   - encoding: mechanism on the restricted common-prefix report domain → full-domain mechanism with LT required only on the common-prefix domain; reason: arbitrary feasible lotteries extend every restricted mechanism outside that domain, with no extra LT constraint
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 3.1, equation (2), PDF p. 8 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_prefixList

open scoped BigOperators ENNReal Topology
open Filter

namespace HouseAllocLT.LowerBound

/-- Lemma 3.1, PDF p.8 (printed p.6), equation (2).
The report q has paper length q+1, and object j is paper object a_(j+1).
Only the other agents' entries of P are constrained, since P i is replaced. -/
theorem lemma_3_1 {n : ℕ} (hn : 1 ≤ n) (φ : Mechanism n n)
    (hφ : IsLTOn φ (prefixDomain n)) (i : Fin n) (P : Profile n n)
    (hP : ∀ k, k ≠ i → P k ∈ prefixDomain n)
    (j q q' : Fin n) (hq : j ≤ q) (hq' : j ≤ q') :
    marginal φ (Function.update P i (prefixList q)) i j =
      marginal φ (Function.update P i (prefixList q')) i j := by sorry

end HouseAllocLT.LowerBound
