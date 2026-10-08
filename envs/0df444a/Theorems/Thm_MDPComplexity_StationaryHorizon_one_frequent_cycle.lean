-- Prove2me | Theorems.Thm_MDPComplexity_StationaryHorizon_one_frequent_cycle
-- name    : MDPComplexity.StationaryHorizon.one_frequent_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:44:57.092977+00:00
-- url     : https://prove2.me/theorems/d02b1d76-0d4b-453c-a9e0-715755df1ba6
-- title:
--   Corrected exchange claim: at most one simple cycle occurs more than n times
-- statement:
--   Let $M$ have $n$ states, with arbitrary real decision costs, and fix an initial state $s_0$ and a horizon $T$. Some cheapest $T$-arc walk from $s_0$ has a decomposition into a simple path and simple cycles in which any cycle occurring more than $n$ times has the least mean cost among the cycles in that decomposition, and no two distinct cycles each occur more than $n$ times.
--
--   The claim controls the repeated cycles that appear in the finite-horizon structure argument.
--
--   **Formalization Note** The paper prints an exchange that repeats the lower-mean cycle fewer times and the other cycle more times, reversing the cost inequality. The cost-reducing exchange runs in the opposite direction. The conclusion uses “more than $n$” to leave a copy of a cycle in place when other cycles attach there. Equality of recorded cycles includes their chosen decision arcs, so parallel arcs remain distinct.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 447, §3 The finite horizon, stationary case, exchange paragraph (corrected), https://doi.org/10.1287/moor.12.3.441

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447, exchange claim, corrected: a minimum-cost `T`-arc walk has a
decomposition in which at most one simple cycle occurs more than `n` times. -/
theorem one_frequent_cycle (M : DetMDP S) (s₀ : S) (T : ℕ) :
    ∃ (W : M.Walk T), W.x 0 = s₀ ∧
      IsLeast {y : ℝ | ∃ V : M.Walk T, V.x 0 = s₀ ∧ y = V.cost} W.cost ∧
      ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)),
        M.IsCycleDecomposition W P Cs ∧
        ∀ C₁ ∈ Cs, ∀ C₂ ∈ Cs,
          Fintype.card S < Set.ncard {i : Fin Cs.length | Cs[i] = C₁} →
          (C₁.2.cost / (C₁.1 : ℝ) ≤ C₂.2.cost / (C₂.1 : ℝ)) ∧
          (Fintype.card S < Set.ncard {i : Fin Cs.length | Cs[i] = C₂} → C₁ = C₂) := by sorry

end MDPComplexity.StationaryHorizon
