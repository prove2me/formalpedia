-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_eq3_bayes_update
-- name    : HumanMachine.Accuracy.eq3_bayes_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:57.21704+00:00
-- url     : https://prove2.me/theorems/5691fc78-683c-4953-b823-1195f9c10953
-- title:
--   (3) — the machine's output updates the DM's belief to $\mu^-=0$ and $\mu^+=\mu/(\mu+\pi(+,-))>\mu$
-- statement:
--   Let $\pi$ be a prior on $(x_1,x_2)\in\{-,+\}^2$ with every entry positive, let $\mu=\pi(+,+)$ be the DM's prior belief that the state is good, and let $\mu^x$ be her Bayes-updated belief after the machine reports $X_1=x$. Then
--
--   $$\mu^-=0\qquad\text{and}\qquad \mu^+=\frac{\mu}{\mu+\pi(+,-)}>\mu.$$
--
--   A negative machine output reveals that the state is bad, while a positive one raises the DM's belief in the good state. Every machine-assisted metric of the paper is an average of a DM-alone metric at these two beliefs.
--
--   **Formalization Note** $\mu$ is `priorGood π`, which is $\pi(+,+)$ written as the prior mass of the good state.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 10, §3.2, equation (3)

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel
import Definitions.Def_HumanMachine_Accuracy_Machine

namespace HumanMachine.Accuracy

/-- Equation (3) (p. 10): with a positive prior `π` on `(x₁, x₂) ∈ {−, +}²` and `μ = π(+, +)`,
Bayes' rule gives the updated beliefs `μ⁻ = 0` and `μ⁺ = μ / (μ + π(+, −)) > μ`. -/
theorem eq3_bayes_update (π : Bool → Bool → ℝ) (hπ : IsPrior π) :
    posterior π false = 0 ∧
      posterior π true = priorGood π / (priorGood π + π true false) ∧
      priorGood π < posterior π true := by sorry

end HumanMachine.Accuracy
