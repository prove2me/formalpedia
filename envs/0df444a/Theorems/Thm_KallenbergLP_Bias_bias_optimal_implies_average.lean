-- Prove2me | Theorems.Thm_KallenbergLP_Bias_bias_optimal_implies_average
-- name    : KallenbergLP.Bias.bias_optimal_implies_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:04:45.408362+00:00
-- url     : https://prove2.me/theorems/c884cd2e-de6e-435d-b101-40e17411a143
-- title:
--   Theorem 5.2.1 — bias optimality implies average optimality, but not conversely
-- statement:
--   In every finite stochastic Markov decision model, any bias optimal policy $R$ is average optimal:
--
--   $$
--   \bigl[\forall i,\ \lim_{\beta\uparrow1}(v_i^\beta(R)-v_i^\beta)=0\bigr]
--   \quad\Longrightarrow\quad
--   \bigl[\forall i,\ \phi_i(R)=\phi_i\bigr].
--   $$
--
--   The converse fails in general: a two-state model with a pure stationary average optimal policy that is not bias optimal exists. Thus bias optimality distinguishes policies that the average-reward criterion can tie.
--
--   **Formalization Note** The first clause quantifies over all history-dependent randomized policies. The existence clause expresses the two-state counterexample in Figure 5.2.1; it does not presume that every average optimal policy is pure stationary.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 163–164, Theorem 5.2.1 and Figure 5.2.1; https://ir.cwi.nl/pub/13008

import Definitions.Def_KallenbergLP_Bias_Criteria

namespace KallenbergLP.Bias

/-- Theorem 5.2.1 (pp. 163–164), including the two-state counterexample. -/
theorem bias_optimal_implies_average {N : ℕ} {α : Type}
    [Fintype α] [DecidableEq α] (M : MDP N α) :
    (∀ R : Policy M, IsBiasOptimal M R → IsAverageOptimal M R) ∧
    (∃ (M' : MDP 2 (Fin 2)) (f : PureRule M'),
      IsAverageOptimal M' (purePolicy M' f) ∧
        ¬ IsBiasOptimal M' (purePolicy M' f)) := by sorry

end KallenbergLP.Bias
