-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_Supplement_all_pairs_second_mincuts
-- name    : MSTCuts2027.Parallel.Supplement.all_pairs_second_mincuts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:41:58.107047+00:00
-- url     : https://prove2.me/theorems/ea24a13e-0e00-46d7-94cf-84f164067f0d
-- title:
--   Theorem 4 — all-pairs second mincuts from a mincut cover (corrected: additive $O(n^2\log n)$ term)
-- statement:
--   There are a program and constants $c,k$ such that the following holds for every $n$ and every symmetric real cut function $F$ on $n$ vertices for which every pair of distinct vertices has a second mincut. Let $Q$ be a correct single-pair second-mincut procedure whose work on every pair of distinct vertices is at most $T_2$. Let the memory hold the input: the number $n$, and for every ordered pair of distinct vertices a pointer to a $(u,v)$-mincut together with the value $\lambda_1(u,v)$ (a mincut cover for all pairs). Then the program, on the machine of word size $(n+2)^k$ with procedure $Q$, halts and leaves in memory, for every ordered pair of distinct vertices, a pointer to a second $(u,v)$-mincut and the value $\lambda_2(u,v)$. For $n\ge2$ its work $W$ satisfies, with $L=\lceil\log_2 n\rceil$,
--   $$W\le c\,\bigl(n L\,T_2+n^2L\bigr),\qquad\text{and}\qquad W\le c\,nL\,T_2\ \text{ whenever } T_2\ge n.$$
--
--   This is the first algorithm for all-pairs second mincuts for arbitrary symmetric cut functions; it uses $O(n\log n)$ second-mincut computations, which matches the size of the second mincut cover of Baswana and Roy (2026).
--
--   Differences from the source:
--   - correction: O(n log n T2(s,t)) time → work at most c(nL·T2 + n²L), and at most c·nL·T2 when T2 ≥ n; reason: the printed bound fails when T2 < n; a procedure of work 0 gives the bound 0, while the output has a second-mincut pointer for each of the n(n−1) ordered pairs and the input memory may hold none of them; the proof (§5.5) bounds the time by O(n log n) second-mincut computations plus O(n² log n)
--   - encoding: there exists an algorithm with a time bound → there exist one program and constants c, k fixed before the instance, with the work of its run on the machine of word size (n+2)^k; reason: the paper gives no numerical constant; the program may depend on nothing in the instance
--   - encoding: T2(s,t), the time of computing a second (s,t)-mincut → a common bound T2 on the work of the procedure Q over all pairs of distinct vertices; reason: the bound must hold for every query the algorithm makes
--   - reading: given a mincut cover for all pairs → the table M of Appendix D with a mincut pointer and the value λ1 for every ordered pair of distinct vertices; reason: the algorithm sorts the mincut values (§5.5) and a cut function cannot be evaluated in the machine; the paper stores the cover in C with the pointers M (§5.4, Appendix D)
--   - encoding: computes all-pairs second mincuts → a pointer to a second mincut and the value λ2 for every ordered pair of distinct vertices; reason: same output as the mincut output of Theorem 3
--   - encoding: log n → ⌈log₂ n⌉ (Nat.clog 2 n), for n ≥ 2; reason: for n ≤ 1 there are no pairs and log n is 0
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Theorem 4, printed p. 4, PDF p. 6; proof §5.4–5.5, printed p. 15, PDF p. 17; Algorithm 7, printed p. 16, PDF p. 18; Appendix D.2, printed pp. 23–24, PDF pp. 25–26

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondAlgorithms

namespace MSTCuts2027.Parallel.Supplement

open MSTCuts2027.Parallel

/-- Theorem 4 (All-Pairs Second Mincuts), corrected bound: one fixed program, with constants fixed
before the input, receives a mincut pointer and the mincut value for every ordered pair of distinct
vertices and a second-mincut procedure `Q` of per-query work at most `T₂`, and writes a
second-mincut pointer and `λ₂` for every ordered pair of distinct vertices, in work
`O(n log n · T₂ + n² log n)`, which is `O(n log n · T₂)` whenever `T₂ ≥ n`. -/
theorem all_pairs_second_mincuts :
    ∃ (A : Program) (entry c k : ℕ), ∀ (n : ℕ) (F : Finset (Fin n) → ℝ),
      IsSymmetricCutFunction F → SecondMincutsExist F →
      ∀ Q : Oracle ℝ n, IsSecondMincutOracle F Q →
      ∀ T₂ : ℕ, (∀ u v : Fin n, u ≠ v → (Q u v).work ≤ T₂) →
      ∀ σ : Store ℝ, IsReady n σ → TableOK F σ Finset.univ →
        ∃ o : Outcome ℝ,
          Halts (⟨(n + 2) ^ k, Q⟩ : Machine ℝ n) A entry [] σ o ∧
          AllPairsSecondOutput F o.store ∧
          (2 ≤ n →
            o.work ≤ c * (n * Nat.clog 2 n * T₂ + n ^ 2 * Nat.clog 2 n) ∧
            (n ≤ T₂ → o.work ≤ c * (n * Nat.clog 2 n * T₂))) := by sorry

end MSTCuts2027.Parallel.Supplement
