-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_satisfiesDummy_of_symmetric_marginal
-- name    : MonotonicSolutions.StrongMono.satisfiesDummy_of_symmetric_marginal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:06:41.212293+00:00
-- url     : https://prove2.me/theorems/fc999802-d5e4-41d6-8592-e7fc22d8810f
-- title:
--   Eq. (8) — dummy players get nothing
-- statement:
--   Let $\varphi$ be an allocation procedure on the games on $N = \{1, \dots, n\}$ (so $\sum_{i \in N} \varphi_i(v) = v(N)$ for every game $v$) that is symmetric and satisfies the marginality condition (7). Then for every game $v$ and every player $i$,
--   $$v^i(S) = 0 \text{ for all } S \subseteq N \quad \Longrightarrow \quad \varphi_i(v) = 0. \tag{8}$$
--
--   That is, dummy players get nothing. In the paper this is derived from (7) by comparing $v$ with the identically zero game, whose allocation is zero by symmetry and efficiency.
--
--   **Formalization Note** The hypothesis is marginality (7) rather than strong monotonicity (6), exactly as the paper's derivation ("By (7) it follows"); by Eq. (7) the statement applies in particular to every strongly monotonic procedure.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, Eq. (8)

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Eq. (8) of Young (1985, p. 70): for a symmetric allocation procedure `φ` satisfying (7),
dummy players get nothing: for every game `v` and player `i`, `v^i(S) = 0` for all `S`
implies `φ_i(v) = 0`. -/
theorem satisfiesDummy_of_symmetric_marginal {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hA : IsAllocationProcedure φ) (hS : IsSymmetric φ) (hM : IsMarginal φ) :
    SatisfiesDummy φ := by sorry

end MonotonicSolutions.StrongMono
