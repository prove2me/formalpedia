-- Prove2me | Theorems.Thm_NQueensComp_NPC_theorem_2
-- name    : NQueensComp.NPC.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:33.675689+00:00
-- url     : https://prove2.me/theorems/57ab480b-4633-4baa-b869-5cb7abd4eaa9
-- title:
--   Theorem 2 (Pólya) — a modular n-Queens solution n-embedded along an m-Queens solution solves (n·m)-Queens
-- statement:
--   **Theorem 2 (Pólya).** If $Q_1$ is a modular solution to the $n$-Queens problem and $Q_2$ is any solution to the $m$-Queens problem, then
--   $$Q_1+nQ_2=\{q_1+nq_2\mid q_1\in Q_1,\ q_2\in Q_2\}$$
--   is a solution to the $n\times m$-Queens problem, i.e. to the $(nm)$-Queens problem.
--
--   In chessboard terms: replace every empty square of an $m$-Queens solution by an empty $n\times n$ board and every queen by a modular $n$-Queens solution. The reduction of Definition 10 builds its frame this way from $Q_{19}$ and $A_{n'}$.
--
--   Differences from the source:
--   - encoding: the n × m-Queens problem → the (n·m)-Queens problem `IsNQueensSol (n * m)`; reason: the paper's n × m board is the board of size nm (it replaces each square of an m × m board by an n × n board)
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 819, Theorem 2 (Bell & Stevens 2009, Thm. 6)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Theorem 2 (Pólya), p. 819: if `Q₁` is a modular solution to the `n`-Queens problem and `Q₂`
is a solution to the `m`-Queens problem, then `Q₁ + nQ₂` is a solution to the `(n·m)`-Queens
problem. -/
theorem theorem_2 (n m : ℕ) (Q₁ Q₂ : Finset Queen) (h₁ : IsModularSol n Q₁)
    (h₂ : IsNQueensSol m Q₂) : IsNQueensSol (n * m) (sumSet Q₁ (scaleSet n Q₂)) := by sorry

end NQueensComp.NPC
