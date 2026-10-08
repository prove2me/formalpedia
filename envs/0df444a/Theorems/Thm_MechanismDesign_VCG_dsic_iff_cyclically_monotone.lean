-- Prove2me | Theorems.Thm_MechanismDesign_VCG_dsic_iff_cyclically_monotone
-- name    : MechanismDesign.VCG.dsic_iff_cyclically_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:16:58.208414+00:00
-- url     : https://prove2.me/theorems/e749ccf4-9c14-4400-b9b5-3483771b7507
-- title:
--   Proposition 7.1 -- dominant-strategy implementability iff cyclical monotonicity in each agent's type (Rochet)
-- statement:
--   In the dominant-strategy model of Chapter 7 (finite agent set $I$, alternatives $A$, abstract type sets $\Theta_i$, quasilinear utilities $u_i(a,\theta_i) - t_i$), let $q : \Theta \to A$ be a decision rule. There are transfer rules $t_1, \dots, t_N$ making $(q, t_1, \dots, t_N)$ dominant strategy incentive-compatible if and only if, for every agent $i$, every $\theta_{-i} \in \Theta_{-i}$ and every finite sequence of types $\theta_i^1, \theta_i^2, \dots, \theta_i^k \in \Theta_i$ with $\theta_i^k = \theta_i^1$,
--
--   $$
--   \sum_{\kappa=1}^{k-1} \Big( u_i(a^\kappa, \theta_i^{\kappa+1}) - u_i(a^\kappa, \theta_i^\kappa) \Big) \le 0, \qquad a^\kappa = q(\theta_i^\kappa, \theta_{-i}).
--   $$
--
--   This is Rochet's (1987) characterization of implementable decision rules, applied separately to each agent and each profile of the other agents' types. No structure on $A$ or on the type sets is needed.
--
--   **Formalization Note** A sequence of length $k+1$ is `θs : Fin (k + 1) → Θ i` with `θs (Fin.last k) = θs 0`, and the sum runs over its $k$ consecutive steps; every $k \in \mathbb N$ is allowed. The profile $\theta_{-i}$ is given as a full profile `θ` whose $i$-th coordinate is overwritten.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.131–132, Proposition 7.1

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.1 (pp.131–132), Rochet's theorem for dominant strategies: a decision
rule `q` is part of a dominant strategy incentive-compatible direct mechanism if and only if, for
every agent `i`, every `θ₋ᵢ`, and every sequence of types `θ¹ᵢ, …, θᵏᵢ` of agent `i` with
`θᵏᵢ = θ¹ᵢ`, `∑_{κ=1}^{k-1} (uᵢ(aᵏ, θᵏ⁺¹ᵢ) − uᵢ(aᵏ, θᵏᵢ)) ≤ 0` where `aᵏ = q(θᵏᵢ, θ₋ᵢ)`.
The sequence is `θs : Fin (k + 1) → Θ i` (indices `0, …, k`), and `θ₋ᵢ` is the part of the
profile `θ` other than coordinate `i`. -/
theorem dsic_iff_cyclically_monotone {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j) (k : ℕ) (θs : Fin (k + 1) → Θ i), θs (Fin.last k) = θs 0 →
        ∑ κ : Fin k, (u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.succ)
          - u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.castSucc)) ≤ 0 := by sorry

end MechanismDesign.VCG
