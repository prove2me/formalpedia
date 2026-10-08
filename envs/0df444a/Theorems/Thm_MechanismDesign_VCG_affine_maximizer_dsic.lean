-- Prove2me | Theorems.Thm_MechanismDesign_VCG_affine_maximizer_dsic
-- name    : MechanismDesign.VCG.affine_maximizer_dsic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:18:12.645993+00:00
-- url     : https://prove2.me/theorems/a96d80a5-f2c1-4845-8f9d-9fe7e70af562
-- title:
--   Proposition 7.8 -- affine maximizers with positive weights are dominant-strategy implementable
-- statement:
--   In the setting of Proposition 7.7 — $A$ finite, and for every agent $i$ and every $\nu \in \mathbb R^A$ some type $\theta_i$ with $u_i(\cdot, \theta_i) = \nu$ — suppose the decision rule $q$ satisfies the characterization of Proposition 7.7: there are weights $k_i > 0$ and a function $F : A \to \mathbb R$ such that for every $\theta \in \Theta$
--
--   $$
--   \sum_{i=1}^N k_i\, u_i(q(\theta), \theta_i) + F(q(\theta)) \ \ge\ \sum_{i=1}^N k_i\, u_i(a, \theta_i) + F(a) \qquad \text{for all } a \in A.
--   $$
--
--   Then there are transfer rules $t_1, \dots, t_N$ such that $(q, t_1, \dots, t_N)$ is dominant strategy incentive-compatible.
--
--   This is the weighted generalization of the VCG construction: affine maximizers are implementable in dominant strategies.
--
--   **Formalization Note** The hypotheses are exactly the page's: the characterization with $k_i > 0$ and all $a \in A$, in the setting of Proposition 7.7 (finite $A$, unrestricted domains). Flexibility is not assumed, and neither finiteness nor the domain condition is needed for the conclusion.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.136, Proposition 7.8 (transfers (7.2), pp.136–137)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.8 (p.136): in the setting of Proposition 7.7 (`A` finite, every
agent's type set unrestricted), suppose `q` satisfies the characterization of Proposition 7.7:
there are `kᵢ > 0` and `F : A → ℝ` with
`∑ᵢ kᵢ uᵢ(q(θ), θᵢ) + F(q(θ)) ≥ ∑ᵢ kᵢ uᵢ(a, θᵢ) + F(a)` for all `θ ∈ Θ` and all `a ∈ A`.
Then there are transfer rules making `(q, t₁, …, t_N)` dominant strategy incentive-compatible. -/
theorem affine_maximizer_dsic {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    [Finite A] (u : ∀ i, A → Θ i → ℝ)
    (hrich : ∀ (i : ι) (ν : A → ℝ), ∃ x : Θ i, ∀ a, u i a x = ν a)
    (q : (∀ i, Θ i) → A) (k : ι → ℝ) (hk : ∀ i, 0 < k i) (F : A → ℝ)
    (hmax : ∀ (θ : ∀ j, Θ j) (a : A),
      ∑ i, k i * u i (q θ) (θ i) + F (q θ) ≥ ∑ i, k i * u i a (θ i) + F a) :
    ∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩ := by sorry

end MechanismDesign.VCG
