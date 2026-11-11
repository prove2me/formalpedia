-- Prove2me | Theorems.Thm_GeneralizedSortingFourCycles_Sorting_generalized_sorting_four_cycles
-- name    : GeneralizedSortingFourCycles.Sorting.generalized_sorting_four_cycles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:18.261231+00:00
-- url     : https://prove2.me/theorems/51c30d4d-57cf-414f-9207-45cdcf383310
-- title:
--   Theorem 1 / Lemma 9 — polynomial-time generalized sorting
-- statement:
--   There is a single randomized finite program, a constant $C>0$, and natural constants $K>0,d$, all independent of the input graph and hidden order, with the following property. Let $G$ be any simple graph on $n$ labeled vertices and let $\pi$ be an unknown total order whose consecutive vertices are adjacent in $G$. The program receives only $G$ and independent unbiased random bits. Its only access to $\pi$ is by comparing allowed edges.
--
--   Every run halts within $K(n+1)^d$ bit-machine transitions, issues only graph-edge comparisons, and, for $n\ge2$, uses at most
--   $$C n^{4/3}(\ln n)^{4/3}$$
--   comparisons. With probability at least
--   $$1-\frac1n,$$
--   it outputs both the increasing vertex list and the direction of every edge. For $n=0,1$ it succeeds surely and makes no comparisons. Runs terminated by a resource cap may fail and are included in the failure probability.
--
--   This is the full paper target, combining the model in §1 with the explicit output of Lemma 9. It claims existence and guarantees as conclusions; it grants the program no order advice and makes no hypothesis of algorithmic correctness.
--
--   Differences from the source:
--   - encoding: a randomized polynomial-time allowed-edge comparison algorithm on a finite graph → one fixed finite sequential bit-machine table; public adjacency input; empty advice and guess tapes; every transition and comparison counted; reason: makes the computational and information restrictions explicit without changing the graph domain
--   - reading: the asymptotic query bound and success probability in Theorem 1 and Lemma 9 → a global constant valid for every n ≥ 2; polynomial time and query cap on every run; cap exhaustion is failure; reason: the source good-event bounds permit capping unsuccessful runs; finite initial sizes are absorbed into the global constants
--   - encoding: the hidden total order and all edge directions → a self-delimiting vertex list and a row-major direction matrix on Fin n; n=0,1 handled by sure zero-query success; reason: finite relabeling and explicit serialization preserve both output requirements and the degenerate instances
-- source:
--   Soheil Behnezhad, Shane Ferrante, STOC 2027 submission #1354 (October 2026), Theorem 1, printed p. 1 (PDF p. 2); Lemma 9, printed p. 15 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1354.pdf

import Mathlib
import Definitions.Def_GeneralizedSortingFourCycles_Sorting_MachineModel

namespace GeneralizedSortingFourCycles.Sorting

/-- Behnezhad–Ferrante, STOC 2027 submission #1354, Theorem 1, printed p. 1
(PDF p. 2), expanded by Lemma 9, printed p. 15 (PDF p. 16).
One finite program and global constants precede every instance. Time counts bit-machine
transitions. Every run halts within the polynomial budget, makes only allowed queries,
and respects the query cap; exhaustion may produce an incorrect output. Correct output
includes the order and every edge direction. The zero/singleton cases succeed surely.
There is no claim that the program witness or its proof has been constructed here. -/
theorem generalized_sorting_four_cycles :
    ∃ (M : NKtLB.Machine) (C : ℝ) (K d : ℕ),
      0 < C ∧ 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)),
        GenSort.Promise G π →
        let T := K * (n + 1) ^ d
        (∀ ω : Fin (T + 1) → Bool,
          let inp := sortingInputs G ω
          (M.run (comparisonOracle G π) inp T).state = M.halt ∧
          LegalRun M G π inp T ∧
          (if n ≤ 1 then comparisonCount M (comparisonOracle G π) inp T = 0
           else (comparisonCount M (comparisonOracle G π) inp T : ℝ) ≤ C * queryScale n)) ∧
        (if n ≤ 1 then (1 : ℝ) else 1 - 1 / (n : ℝ)) ≤
          fairProbability (T + 1) (fun ω =>
            M.HaltsWith (comparisonOracle G π) (sortingInputs G ω) T
              (NKtLB.bitsSym (sortingWord G π))) := by sorry

end GeneralizedSortingFourCycles.Sorting
