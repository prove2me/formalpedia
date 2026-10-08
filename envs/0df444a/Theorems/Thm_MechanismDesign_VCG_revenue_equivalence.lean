-- Prove2me | Theorems.Thm_MechanismDesign_VCG_revenue_equivalence
-- name    : MechanismDesign.VCG.revenue_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:18:02.926242+00:00
-- url     : https://prove2.me/theorems/409cc9c7-376d-4690-820e-2b06caad3769
-- title:
--   Proposition 7.3 -- dominant-strategy transfers are unique up to terms in the others' types (Krishna–Maenner)
-- statement:
--   In the dominant-strategy model of Chapter 7, suppose that for every agent $i$ the type set $\Theta_i$ is a convex subset of a finite-dimensional Euclidean space $\mathbb R^{d_i}$, and that for every alternative $a$ the function $\theta_i \mapsto u_i(a, \theta_i)$ is convex and continuous on $\Theta_i$. Suppose $(q, t_1, \dots, t_N)$ is dominant strategy incentive-compatible. Then a direct mechanism $(q, t_1', \dots, t_N')$ with the same decision rule is dominant strategy incentive-compatible if and only if for every agent $i$ there is a function $\tau_i : \Theta_{-i} \to \mathbb R$ such that
--
--   $$
--   t_i'(\theta) = t_i(\theta) + \tau_i(\theta_{-i}) \qquad \text{for all } \theta \in \Theta .
--   $$
--
--   This is the payoff (revenue) equivalence theorem of Krishna and Maenner (2001) in its dominant-strategy form: given the decision rule, each agent's transfer is pinned down up to a term that his own report cannot influence.
--
--   **Formalization Note** The book assumes only that $u_i(a,\cdot)$ is convex; continuity on $\Theta_i$ is added because the statement is false without it. Counterexample: one agent, $\Theta_1 = [0,1] \subset \mathbb R$, $A = \{a, b\}$, $u_1(a, \cdot) = 0$, $u_1(b, \theta) = 1$ if $\theta = 1$ and $0$ otherwise (convex on $[0,1]$, discontinuous at $1$), $q(\theta) = b$ iff $\theta = 1$; then $t_1 = 0$ and $t_1'(\theta) = \tfrac12 \cdot [\theta = 1]$ are both DSIC but differ by a non-constant function of $\theta_1$. The type set of agent $i$ is the subtype of a set `S i` in `EuclideanSpace ℝ (Fin (d i))`; utilities are functions on the whole space of which only the values on `S i` matter. $\tau_i$ is a function on `Others`, the product of the other agents' type sets.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.132, Proposition 7.3 (continuity of u_i(a,·) added; see Formalization Note)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.3 (p.132), after Krishna and Maenner (2001), with continuity added
(see the natural-language statement): each type set `Θᵢ = Sᵢ` is a convex subset of the
Euclidean space `ℝ^{dᵢ}` and each `uᵢ(a, ·)` is convex and continuous on `Sᵢ`. If
`(q, t₁, …, t_N)` is dominant strategy incentive-compatible, then `(q, t'₁, …, t'_N)` is dominant
strategy incentive-compatible if and only if for every `i` there is `τᵢ : Θ₋ᵢ → ℝ` with
`t'ᵢ(θ) = tᵢ(θ) + τᵢ(θ₋ᵢ)` for all `θ ∈ Θ`. -/
theorem revenue_equivalence {ι A : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (S : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) (hS : ∀ i, Convex ℝ (S i))
    (u : ∀ i, A → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (hconv : ∀ i a, ConvexOn ℝ (S i) (u i a))
    (hcont : ∀ i a, ContinuousOn (u i a) (S i))
    (M : DirectMechanism (fun i => ↥(S i)) A)
    (hM : DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M)
    (t' : ι → (∀ i, ↥(S i)) → ℝ) :
    DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) ⟨M.q, t'⟩ ↔
      ∀ i : ι, ∃ τ : Others (fun i => ↥(S i)) i → ℝ,
        ∀ θ : ∀ j, ↥(S j), t' i θ = M.t i θ + τ (restrict θ i) := by sorry

end MechanismDesign.VCG
