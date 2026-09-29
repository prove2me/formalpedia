-- Prove2me | Theorems.Thm_MarkovEntanglement_cooperative_decomposition_error_with_reward_entanglement
-- name    : MarkovEntanglement.cooperative_decomposition_error_with_reward_entanglement
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T13:55:02.087571+00:00
-- url     : https://prove2.me/theorems/9a4891a1-28d8-4be6-8313-800d44e862e4
-- title:
--   Shared rewards add a reward-entanglement term to the error
-- statement:
--   ## Statement
--
--   **Proposition.** For a fully cooperative system whose global reward need not decompose,
--   let $e(r)$ be the measure of reward entanglement, the $\mu$-norm distance from $r$ to the
--   nearest sum of local rewards. Then
--   $$\Bigl\| Q^\pi - \sum_{i=1}^N Q^\pi_i \Bigr\|_{\mu^\pi}
--   \;\le\; \frac{e(r)}{1-\gamma}
--      \;+\; \frac{4\gamma \sum_{i=1}^N \mathcal{E}_i(P^\pi)\, r^i_{\max}}{(1-\gamma)^2}.$$
--
--   ## Notes
--
--   The main bound assumes the reward already splits across agents. In genuinely cooperative
--   problems it usually does not — there is one shared reward — and this proposition covers that
--   case by adding a second source of error.
--
--   The two terms separate cleanly and are worth reading side by side. **Reward entanglement**
--   enters with a single factor $(1-\gamma)^{-1}$, because a reward misfit is a zeroth-order error
--   that is merely summed along the trajectory. **Transition entanglement** enters with
--   $(1-\gamma)^{-2}$, because a one-step transition error compounds through the value recursion.
--   So an imperfectly decomposable reward is the milder of the two defects.
--
--   Search terms: shared reward multi-agent, reward decomposition error, cooperative MARL value
--   decomposition, credit assignment error bound.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Proposition 4, p. 48

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem cooperative_decomposition_error_with_reward_entanglement
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : Joint S → ℝ) (rl : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |rl i s| ≤ rmax i)
    -- `rl` must attain the measure of reward entanglement, exactly as `Pl` attains
    -- the measure of Markov entanglement; without this the local rewards are free
    -- and the bound is false.
    (hrl : muNorm μ (fun p => r p - ∑ i, rl i (p i)) = rewardEntanglement μ r)
    (hQ : IsBellmanQ P r γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, muAgentTVDistN i μ P (Pl i) = entanglementN i μ P)
    (hQi : ∀ i, IsBellmanQ (Pl i) (rl i) γ (Qi i)) :
    muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ rewardEntanglement μ r / (1 - γ)
        + 4 * γ * (∑ i, entanglementN i μ P * rmax i) / (1 - γ) ^ 2 := by
  sorry

end MarkovEntanglement
