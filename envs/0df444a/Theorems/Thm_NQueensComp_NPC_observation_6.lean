-- Prove2me | Theorems.Thm_NQueensComp_NPC_observation_6
-- name    : NQueensComp.NPC.observation_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:26.192571+00:00
-- url     : https://prove2.me/theorems/ccea96b9-b1b8-4dde-b4fa-b6fbff73ef7c
-- title:
--   Observation 6 — the properties of Q₁₉
-- statement:
--   **Observation 6.** The set $Q_{19}$ of Definition 5 satisfies:
--   1. it is a solution to the 19-Queens problem;
--   2. it has no queen on difference-diagonals $1$, $0$ or $-1$;
--   3. for its queens $(0,8)$ and $(17,0)$ consider the squares $(19,8)$ and $(17,19)$: their sum-diagonals are not within $1$ of each other, of $(0,0)$ or of any queen of $Q_{19}$, and the same holds for their difference-diagonals:
--   $$|\Sigma(m)-\Sigma(p)|>1,\quad |\Delta(m)-\Delta(p)|>1\qquad(m\in\{(19,8),(17,19)\},\ p\in Q_{19}\cup\{(0,0)\}),$$
--   and $|\Sigma(19,8)-\Sigma(17,19)|>1$, $|\Delta(19,8)-\Delta(17,19)|>1$.
--
--   These are the properties of the 19-queens frame that the reduction of Definition 10 uses through Lemma 9.
--
--   Differences from the source:
--   - reading: “their sum-/difference-diagonals are not within 1 of each other, (0, 0) or any queen in Q₁₉” → sum-diagonals are compared with sum-diagonals and difference-diagonals with difference-diagonals, each difference at least 2 in absolute value; reason: the “sum-/difference-” notation is used respectively throughout the paper (Lemma 9)
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 822, Observation 6 (Definition 5)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Observation 6, p. 822: `Q₁₉` is a solution to the 19-Queens problem; it has no queen on
difference-diagonals `1, 0, −1`; for its queens `(0, 8)` and `(17, 0)` consider `(19, 8)` and
`(17, 19)`: their sum-diagonals (respectively difference-diagonals) are not within `1` of each
other, of `(0, 0)` or of any queen of `Q₁₉`. -/
theorem observation_6 :
    IsNQueensSol 19 Q19 ∧
    (∀ q ∈ Q19, diffDiag q ≠ 1 ∧ diffDiag q ≠ 0 ∧ diffDiag q ≠ -1) ∧
    ((0, 8) ∈ Q19 ∧ (17, 0) ∈ Q19) ∧
    (1 < |((sumDiag (19, 8) : ℕ) : ℤ) - ((sumDiag (17, 19) : ℕ) : ℤ)| ∧
      1 < |diffDiag (19, 8) - diffDiag (17, 19)|) ∧
    ∀ m ∈ ({(19, 8), (17, 19)} : Finset Queen), ∀ p ∈ insert ((0, 0) : Queen) Q19,
      1 < |((sumDiag m : ℕ) : ℤ) - ((sumDiag p : ℕ) : ℤ)| ∧
        1 < |diffDiag m - diffDiag p| := by sorry

end NQueensComp.NPC
