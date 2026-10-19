-- Prove2me | Theorems.Thm_InnovContest_Rewards_theorem_2
-- name    : InnovContest.Rewards.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:11.354897+00:00
-- url     : https://prove2.me/theorems/47b8a52c-bdaa-4e31-b1da-3e0f1941b14e
-- title:
--   Theorem 2 (corrected) — when multiple rewards are optimal
-- statement:
--   Fix $n\ge2$ and a common ability distribution on $[0,1]$ with continuous, strictly positive density. The firm maximizes expected best participating submission minus $c_f$ times the probability that nobody enters, over every feasible rank-reward allocation.
--
--   For $c_p=0$, every positive budget and every $c_f\ge0$ admit an optimum, and every optimal allocation has exactly one positive reward. For $c_p>0$, there is a threshold $\widehat c_p>c_p$ such that for every $c_p<B<n c_p$ there is a threshold $\widehat c_f>0$. An optimum exists for every $c_f\ge0$, and:
--
--   $$\begin{aligned}
--   B<\widehat c_p\ \text{or}\ c_f<\widehat c_f&\implies m^*=1,\\
--   \widehat c_p<B\ \text{and}\ \widehat c_f<c_f&\implies 2\le m^*\le m_p^*(B).
--   \end{aligned}$$
--
--   Each conclusion applies to every optimal allocation; $m^*$ counts positive rewards and $m_p^*(B)$ is the largest number of equal awards maximizing participation. The same thresholds govern both clauses.
--
--   **Formalization Note** The upper budget bound is the proof's standing assumption; the strict inequalities in the multi-reward clause avoid boundary ties. The objective is equation (6), and all equilibrium quantities are recomputed for each compared allocation.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), p. 12, Theorem 2; proof pp. 27–29; standing assumption pp. 10, 23 (corrected at boundaries)

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- Theorem 2, p. 12, corrected at the equality boundaries and with the standing
`budget < n * cp` assumption from the proof of Proposition 1 made explicit. -/
theorem theorem_2 (M : AbilityModel) :
    (∀ (budget cf : ℝ), 0 < budget → 0 ≤ cf →
      (∃ r : ℕ → ℝ, IsOptimal M budget 0 cf r) ∧
      (∀ r : ℕ → ℝ, IsOptimal M budget 0 cf r → numRewards M.n r = 1)) ∧
    (∀ cp : ℝ, 0 < cp →
      ∃ cpHat : ℝ, cp < cpHat ∧
        ∀ budget : ℝ, cp < budget → budget < (M.n : ℝ) * cp →
          ∃ cfHat : ℝ, 0 < cfHat ∧
            ∀ cf : ℝ, 0 ≤ cf →
              (∃ r : ℕ → ℝ, IsOptimal M budget cp cf r) ∧
              ((budget < cpHat ∨ cf < cfHat) →
                ∀ r : ℕ → ℝ, IsOptimal M budget cp cf r → numRewards M.n r = 1) ∧
              ((cpHat < budget ∧ cfHat < cf) →
                ∀ r : ℕ → ℝ, IsOptimal M budget cp cf r →
                  2 ≤ numRewards M.n r ∧ numRewards M.n r ≤ mstarP M budget cp)) := by sorry

end InnovContest.Rewards
