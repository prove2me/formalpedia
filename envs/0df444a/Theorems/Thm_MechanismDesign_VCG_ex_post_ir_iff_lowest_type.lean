-- Prove2me | Theorems.Thm_MechanismDesign_VCG_ex_post_ir_iff_lowest_type
-- name    : MechanismDesign.VCG.ex_post_ir_iff_lowest_type
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:18:29.851348+00:00
-- url     : https://prove2.me/theorems/284c33ea-eeaa-46bd-b5bb-d511b37b51cd
-- title:
--   Proposition 7.9 -- ex post individual rationality holds iff it holds at the lowest type
-- statement:
--   In the dominant-strategy model of Chapter 7, fix an agent $i$ and an order $R_i$ (complete and transitive) of $A$, and suppose the type set $\Theta_i$ is one-dimensional with respect to $R_i$. Assume that $\underline\theta_i \in \Theta_i$ is the lowest type, $\theta_i \succ_{R_i} \underline\theta_i$ for every $\theta_i \ne \underline\theta_i$, and that $\underline a_i \in A$ is the lowest alternative, $b\, R_i\, \underline a_i$ for every $b \ne \underline a_i$. Let $(q, t_1, \dots, t_N)$ be dominant strategy incentive-compatible. Then agent $i$'s ex post individual rationality constraint with outside option $\underline a_i$,
--
--   $$
--   u_i(q(\theta), \theta_i) - t_i(\theta) \ge u_i(\underline a_i, \theta_i) \qquad \text{for all } \theta \in \Theta,
--   $$
--
--   holds if and only if for every $\theta_{-i} \in \Theta_{-i}$
--
--   $$
--   u_i(q(\underline\theta_i, \theta_{-i}), \underline\theta_i) - t_i(\underline\theta_i, \theta_{-i}) \ge u_i(\underline a_i, \underline\theta_i).
--   $$
--
--   It is enough to check individual rationality for the lowest type, as in the examples of Chapters 2–4.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.137–138, Proposition 7.9 (with Definition 7.7)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.9 (pp.137–138): fix an agent `i` and an order (complete, transitive)
`R` of `A` such that `Θᵢ` is one-dimensional with respect to `R`. Suppose `θ̲ᵢ` is the lowest
type (`θᵢ ≻_R θ̲ᵢ` for every `θᵢ ≠ θ̲ᵢ`) and `a̲ᵢ` is the lowest alternative (`b R a̲ᵢ` for every
`b ≠ a̲ᵢ`). Then a dominant strategy incentive-compatible mechanism satisfies agent `i`'s ex post
individual rationality constraint with outside option `a̲ᵢ` if and only if
`uᵢ(q(θ̲ᵢ, θ₋ᵢ), θ̲ᵢ) − tᵢ(θ̲ᵢ, θ₋ᵢ) ≥ uᵢ(a̲ᵢ, θ̲ᵢ)` for every `θ₋ᵢ`. -/
theorem ex_post_ir_iff_lowest_type {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (hM : DSIC u M) (i : ι)
    (R : A → A → Prop) (hR : IsCompleteOrder R) (h1d : OneDimensional R (u i))
    (θlow : Θ i) (hθlow : ∀ x : Θ i, x ≠ θlow → HigherType R (u i) x θlow)
    (alow : A) (halow : ∀ b : A, b ≠ alow → R b alow) :
    ExPostIRAgent u M i alow ↔
      ∀ θ : ∀ j, Θ j, u i (M.q (Function.update θ i θlow)) θlow
        - M.t i (Function.update θ i θlow) ≥ u i alow θlow := by sorry

end MechanismDesign.VCG
