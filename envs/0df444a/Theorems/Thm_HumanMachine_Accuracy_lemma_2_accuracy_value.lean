-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_lemma_2_accuracy_value
-- name    : HumanMachine.Accuracy.lemma_2_accuracy_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:58.310358+00:00
-- url     : https://prove2.me/theorems/fba97090-79bf-47ae-b1e4-09686cb50b01
-- title:
--   Lemma 2 (accuracy and value) — $A^\star_m=1-\mu/\mu^++(\mu/\mu^+)A^\star(\mu^+)$, and likewise $V^\star_m$
-- statement:
--   Let $\lambda>0$ be the information cost, $\pi$ a prior on $(x_1,x_2)\in\{-,+\}^2$ with every entry positive, $\mu=\pi(+,+)$, and $\mu^+$ the DM's belief after a positive machine output. The machine-assisted accuracy and expected value satisfy
--
--   $$A^\star_m=1-\frac{\mu}{\mu^+}+\frac{\mu}{\mu^+}A^\star(\mu^+),\qquad V^\star_m=1-\frac{\mu}{\mu^+}+\frac{\mu}{\mu^+}V^\star(\mu^+).$$
--
--   Both metrics with the machine are thus determined by the two parameters $\mu$ and $\mu^+$. Lemma 2 of the paper also gives the choice probability, error rates and cognitive cost in the same form; those parts are not part of this statement.
--
--   **Formalization Note** $A^\star_m$ and $V^\star_m$ are defined as expectations over the machine's output $x_1$, so this identity is a theorem, not a definition.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 17, Lemma 2 (the A⋆_m and V⋆_m identities)

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel
import Definitions.Def_HumanMachine_Accuracy_Machine

namespace HumanMachine.Accuracy

/-- Lemma 2, accuracy and value parts (p. 17): for information cost `λ > 0` and a positive prior
`π`, with `μ = π(+, +)` and `μ⁺` the belief after a positive machine output,
`A⋆_m = 1 - μ/μ⁺ + (μ/μ⁺) A⋆(μ⁺)` and `V⋆_m = 1 - μ/μ⁺ + (μ/μ⁺) V⋆(μ⁺)`. -/
theorem lemma_2_accuracy_value (lam : ℝ) (hlam : 0 < lam) (π : Bool → Bool → ℝ)
    (hπ : IsPrior π) :
    AStarM lam π = 1 - priorGood π / posterior π true
        + (priorGood π / posterior π true) * AStar lam (posterior π true) ∧
      VStarM lam π = 1 - priorGood π / posterior π true
        + (priorGood π / posterior π true) * VStar lam (posterior π true) := by sorry

end HumanMachine.Accuracy
