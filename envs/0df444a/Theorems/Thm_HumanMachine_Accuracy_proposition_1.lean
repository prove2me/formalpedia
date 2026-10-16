-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_proposition_1
-- name    : HumanMachine.Accuracy.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:04.758441+00:00
-- url     : https://prove2.me/theorems/ebf965c1-5e37-4145-874b-5440f9a86d1b
-- title:
--   Proposition 1 — machine input never lowers the DM's accuracy or expected value: $A^\star_m\ge A^\star$, $V^\star_m\ge V^\star$
-- statement:
--   Let $\lambda\ge0$ be the information cost and $\pi$ a prior on the realizations $(x_1,x_2)\in\{-,+\}^2$ of the machine-observable information $X_1$ and the DM-only information $X_2$, with every entry positive; the state is good iff $x_1=x_2=+$, so the DM's prior belief is $\mu=\pi(+,+)$. Let $A^\star(\mu)$ and $V^\star(\mu)$ be the DM's optimal accuracy and expected value when she decides alone, and $A^\star_m$, $V^\star_m$ their ex-ante values when the machine first reveals $x_1$. Then
--
--   $$A^\star_m\ge A^\star(\mu)\qquad\text{and}\qquad V^\star_m\ge V^\star(\mu).$$
--
--   Because the machine supplies exact information at no cognitive cost, a machine-assisted DM is never less accurate and never worse off than a DM deciding alone, whatever her information cost and prior.
--
--   **Formalization Note** The paper states the result "for all $\lambda\ge0$ and $(\mu,\mu^+)\in\mathcal S$", $\mathcal S=\{(x,y)\in[0,1]^2: x<y\}$; the model's standing assumption is $\lambda>0$ (p. 8), and $\lambda=0$ is kept as printed (the cost then vanishes). Stating the result over a positive prior $\pi$ covers exactly the pairs $0<\mu<\mu^+<1$ of $\mathcal S$; the boundary pairs $\mu=0$ or $\mu^+=1$ are not realised by any prior with positive entries, as the model requires ($\pi(x_1,x_2)>0$, p. 10).
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 17, Proposition 1

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel
import Definitions.Def_HumanMachine_Accuracy_Machine

namespace HumanMachine.Accuracy

/-- Proposition 1 (p. 17): for every information cost `λ ≥ 0` and every positive prior `π` on
`(x₁, x₂) ∈ {−, +}²`, machine input never lowers the DM's accuracy or expected value:
`A⋆_m ≥ A⋆(μ)` and `V⋆_m ≥ V⋆(μ)`, where `μ = π(+, +)`. -/
theorem proposition_1 (lam : ℝ) (hlam : 0 ≤ lam) (π : Bool → Bool → ℝ) (hπ : IsPrior π) :
    AStar lam (priorGood π) ≤ AStarM lam π ∧ VStar lam (priorGood π) ≤ VStarM lam π := by sorry

end HumanMachine.Accuracy
