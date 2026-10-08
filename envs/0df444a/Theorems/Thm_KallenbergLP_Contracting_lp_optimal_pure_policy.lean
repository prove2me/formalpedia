-- Prove2me | Theorems.Thm_KallenbergLP_Contracting_lp_optimal_pure_policy
-- name    : KallenbergLP.Contracting.lp_optimal_pure_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:35:59.789225+00:00
-- url     : https://prove2.me/theorems/f65f7c45-1038-4789-9c61-a3c54318fc14
-- title:
--   Theorem 3.4.3 — an LP optimum yields a pure stationary optimum
-- statement:
--   For strictly positive initial weights $\beta_i$, linear program (3.3.7) has a finite optimal solution $x^*$. If $f$ chooses an action with $x^*_{i f(i)}>0$ in every state, then the pure stationary policy $f^\infty$ is optimal among all policies: for every initial state $i$ and every history-dependent randomized policy $R$,
--
--   $$v_i(R)\le v_i(f^\infty).$$
--
--   Thus the LP optimum supplies one policy that is simultaneously optimal from every initial state.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 64–65, Theorem 3.4.3

import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.3, pp. 64–65. -/
theorem lp_optimal_pure_policy
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M)
    (β : E → ℝ) (hβ : ∀ i, 0 < β i) :
    (∃ x : StationaryRule E A, x ∈ M.feasibleFrequency β ∧
      ∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) ∧
    (∀ x : StationaryRule E A, x ∈ M.feasibleFrequency β →
      (∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) →
      ∀ f : PureRule E A, (∀ i, 0 < x i (f i)) →
        ∀ π : Policy E A, IsPolicy π →
          ∀ i, M.totalReward π i ≤ M.totalReward (purePolicy f) i) := by sorry

end KallenbergLP.Contracting
