-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_exists_unanimity_expansion
-- name    : MonotonicSolutions.StrongMono.exists_unanimity_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:07:44.050202+00:00
-- url     : https://prove2.me/theorems/6152facf-ebf7-4412-a681-00b806139255
-- title:
--   Eq. (9) (quoting Shapley) — every game is a sum of primitive games
-- statement:
--   Let $v$ be a cooperative game on $N = \{1, \dots, n\}$ with $v(\emptyset) = 0$. There are real coefficients $(c_R)_{\emptyset \ne R \subseteq N}$ such that
--   $$v = \sum_{\emptyset \ne R \subseteq N} c_R\, v_R, \tag{9}$$
--   where $v_R$ is the primitive game with $v_R(S) = 1$ if $R \subseteq S$ and $v_R(S) = 0$ otherwise; that is, $v(S) = \sum_{\emptyset \ne R \subseteq S} c_R$ for every coalition $S$.
--
--   Young quotes this fact from Shapley; it is the representation on which the induction in the proof of Theorem 2 runs.
--
--   **Formalization Note** Only existence is asserted, as on the page; the coefficients are indexed by all coalitions but only those of nonempty $R$ enter the sum. The hypothesis $v(\emptyset) = 0$ (part of `Game n`) is needed, since the right-hand side vanishes at $S = \emptyset$.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, Eq. (9) ("the fact noted by Shapley")

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Eq. (9) of Young (1985, p. 70), quoting Shapley: every game `v` (with `v ∅ = 0`) is a
linear combination of primitive games, `v = ∑_{∅ ≠ R ⊆ N} c_R v_R`, where
`v_R(S) = 1` if `R ⊆ S` and `0` otherwise. -/
theorem exists_unanimity_expansion {n : ℕ} (v : Game n) :
    ∃ c : Finset (Fin n) → ℝ, ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S := by sorry

end MonotonicSolutions.StrongMono
