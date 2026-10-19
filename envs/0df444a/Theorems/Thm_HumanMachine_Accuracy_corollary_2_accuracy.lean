-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_corollary_2_accuracy
-- name    : HumanMachine.Accuracy.corollary_2_accuracy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:01.690084+00:00
-- url     : https://prove2.me/theorems/200a9d4c-1c2c-4623-bfd0-4279e27f1f95
-- title:
--   Corollary 2, (13) — the optimal accuracy $A^\star(\mu)$ in closed form
-- statement:
--   Let $\lambda>0$ be the information cost and $\mu\in[0,1]$ the DM's prior belief that the state is good, and let $\underline\mu=1/(e^{1/\lambda}+1)$ and $\bar\mu=e^{1/\lambda}/(e^{1/\lambda}+1)$. The DM's optimal accuracy is
--
--   $$A^\star(\mu)=\begin{cases}1-\mu & \text{if } \mu\le\underline\mu,\\[2pt] \dfrac{e^{1/\lambda}}{e^{1/\lambda}+1} & \text{if } \underline\mu<\mu<\bar\mu,\\[2pt] \mu & \text{if } \mu\ge\bar\mu.\end{cases}$$
--
--   When the prior is extreme the DM processes no information and follows it; in between, her accuracy depends on the information cost only. This is the first display of Corollary 2; the cost display (14) is not part of this statement.
--
--   **Formalization Note** The paper says "Given prior $\mu$"; the statement is made for every $\mu\in[0,1]$, endpoints included (Lemma 2 evaluates $A^\star$ at $\mu^-=0$). $A^\star$ is the accuracy at an optimum of the §4 problem, not the right-hand side above.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 13, Corollary 2, display (13)

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

namespace HumanMachine.Accuracy

/-- Corollary 2, display (13) (p. 13): for information cost `λ > 0` and prior `μ ∈ [0, 1]`,
the optimal accuracy is `A⋆(μ) = 1 - μ` if `μ ≤ μ̲`, `e^{1/λ} / (e^{1/λ} + 1)` if
`μ̲ < μ < μ̄`, and `μ` if `μ ≥ μ̄`. -/
theorem corollary_2_accuracy (lam μ : ℝ) (hlam : 0 < lam) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (μ ≤ HumanMachine.Alone.muLow lam → AStar lam μ = 1 - μ) ∧
      (HumanMachine.Alone.muLow lam < μ → μ < HumanMachine.Alone.muHigh lam →
        AStar lam μ = Real.exp (1 / lam) / (Real.exp (1 / lam) + 1)) ∧
      (HumanMachine.Alone.muHigh lam ≤ μ → AStar lam μ = μ) := by sorry

end HumanMachine.Accuracy
