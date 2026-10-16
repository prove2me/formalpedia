-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_corollary_2_value
-- name    : HumanMachine.Accuracy.corollary_2_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:54.569962+00:00
-- url     : https://prove2.me/theorems/652b2c50-3ca2-4575-b3aa-bed3799a1ecc
-- title:
--   Corollary 2, (15) — the optimal expected value $V^\star(\mu)$ in closed form
-- statement:
--   Let $\lambda>0$ be the information cost, $\mu\in[0,1]$ the DM's prior belief that the state is good, $H$ the binary entropy (natural logarithm), and $\underline\mu=1/(e^{1/\lambda}+1)$, $\bar\mu=e^{1/\lambda}/(e^{1/\lambda}+1)$. The DM's optimal expected value is
--
--   $$V^\star(\mu)=\begin{cases}1-\mu & \text{if } \mu\le\underline\mu,\\[2pt] \lambda\big[\log\big(e^{1/\lambda}+1\big)-H(\mu)\big] & \text{if } \underline\mu<\mu<\bar\mu,\\[2pt] \mu & \text{if } \mu\ge\bar\mu.\end{cases}$$
--
--   In the region where the DM processes information, her expected value falls with the task difficulty $H(\mu)$. This is the third display of Corollary 2.
--
--   **Formalization Note** Stated for every $\mu\in[0,1]$, endpoints included. $V^\star$ is the maximal value of the §4 problem, not the right-hand side above.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 14, Corollary 2, display (15)

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

namespace HumanMachine.Accuracy

/-- Corollary 2, display (15) (p. 14): for information cost `λ > 0` and prior `μ ∈ [0, 1]`,
the optimal expected value is `V⋆(μ) = 1 - μ` if `μ ≤ μ̲`,
`λ [log(e^{1/λ} + 1) - H(μ)]` if `μ̲ < μ < μ̄`, and `μ` if `μ ≥ μ̄`, where `H` is the binary
entropy in nats. -/
theorem corollary_2_value (lam μ : ℝ) (hlam : 0 < lam) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (μ ≤ HumanMachine.Alone.muLow lam → VStar lam μ = 1 - μ) ∧
      (HumanMachine.Alone.muLow lam < μ → μ < HumanMachine.Alone.muHigh lam →
        VStar lam μ = lam * (Real.log (Real.exp (1 / lam) + 1) - Real.binEntropy μ)) ∧
      (HumanMachine.Alone.muHigh lam ≤ μ → VStar lam μ = μ) := by sorry

end HumanMachine.Accuracy
