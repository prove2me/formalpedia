-- Prove2me | Theorems.Thm_OAI_ContingencyTables_counting
-- name    : OAI.ContingencyTables.counting
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:28.379034+00:00
-- url     : https://prove2.me/theorems/5ca70385-d3cb-4806-8df4-1df783c46062
-- statement:
--   The theorem states that there is a single uniform randomized Post-Turing machine A (a finite transition table over an 8-symbol tape alphabet that reads one random bit per step) and natural-number constants C and d with C>0 such that the following holds for all positive dimensions m,n, all row sums r:Fin m→ℕ, column sums c:Fin n→ℕ and cell bounds b:Fin m→Fin n→ℕ with Σᵢrᵢ=Σⱼcⱼ, and all rational accuracy and failure parameters ε,δ with 0<ε<1 and 0<δ<1. Let N be the number of m×n tables of natural numbers with row sums r, column sums c and every entry Xᵢⱼ≤bᵢⱼ. The machine is run on the binary-delimited encoding of m, n, r, c, the matrix b, ε and δ for exactly t=C·(L+⌈1/ε⌉+⌈log₂⌈1/δ⌉⌉+1)^d steps, where L is the length of that input encoding, so the budget is polynomial in the input length and in 1/ε and log(1/δ). Then (1) on every random tape of length t the machine has halted and its output is the encoding of some nonnegative rational q; (2) if N=0, the output is exactly 0 on every random tape; and (3) the fraction of the 2^t random tapes on which the output is a rational q with (1−ε)N≤q≤(1+ε)N is at least 1−δ. This is a fully polynomial randomized approximation scheme for counting contingency tables with cell upper bounds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContingencyTables.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContingencyTables.lean; bytes 9346..9482
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ContingencyTables

namespace OAI

namespace ContingencyTables

/-- A cell-bounded FPRAS, with zero output on every infeasible execution. -/
theorem counting : Algorithms.CountingStatement := by sorry

end ContingencyTables
end OAI
