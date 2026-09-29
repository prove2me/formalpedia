-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_eq_of_primitive_game
-- name    : MonotonicSolutions.StrongMono.eq_of_primitive_game
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:09:13.144155+00:00
-- url     : https://prove2.me/theorems/20d8a752-4b8c-4cea-ade7-1fc6c66ad968
-- title:
--   Base case of Theorem 2 — $\varphi(c_R v_R)$ is the Shapley value
-- statement:
--   Let $\varphi$ be an allocation procedure on the games on $N = \{1, \dots, n\}$ that is symmetric and satisfies the marginality condition (7). Let $R \subseteq N$ be a nonempty coalition, $c_R$ a real number, and $v = c_R v_R$ the game with $v(S) = c_R$ if $R \subseteq S$ and $v(S) = 0$ otherwise. Then for every player $i$,
--   $$\varphi_i(v) = \begin{cases} c_R / |R| & \text{if } i \in R,\\ 0 & \text{if } i \notin R. \end{cases}$$
--
--   This is the case of index $0$ (take $c_R = 0$, the zero game) and index $1$ in the induction proving Theorem 2: on a single primitive game, $\varphi$ coincides with the Shapley value.
--
--   **Formalization Note** The paper's "index" (minimum number of nonzero terms in (9)) is a proof device and is not formalized; the statement quantifies directly over $R$ and $c_R$. The hypothesis is (7), which is what the paper's argument uses (through (8)).
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, proof of Theorem 2 (the cases I = 0 and I = 1)

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 70, proof of Theorem 2, index 1): if `φ` is a symmetric allocation
procedure satisfying (7) and `v = c_R v_R` for a nonempty coalition `R` and a real `c_R`,
then `φ_i(v) = c_R / |R|` for `i ∈ R` and `φ_i(v) = 0` for `i ∉ R`. The case `c_R = 0` is
the zero game (index 0). -/
theorem eq_of_primitive_game {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hA : IsAllocationProcedure φ) (hS : IsSymmetric φ) (hM : IsMarginal φ)
    (R : Finset (Fin n)) (hR : R.Nonempty) (c : ℝ) (v : Game n)
    (hv : ∀ S : Finset (Fin n), v.1 S = c * unanimity R S) (i : Fin n) :
    φ v i = if i ∈ R then c / R.card else 0 := by sorry

end MonotonicSolutions.StrongMono
