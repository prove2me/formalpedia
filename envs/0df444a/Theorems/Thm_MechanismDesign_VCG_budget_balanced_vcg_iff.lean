-- Prove2me | Theorems.Thm_MechanismDesign_VCG_budget_balanced_vcg_iff
-- name    : MechanismDesign.VCG.budget_balanced_vcg_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:18:36.210711+00:00
-- url     : https://prove2.me/theorems/94aaf359-7d06-48a7-aecf-bdb46d1e2f09
-- title:
--   Proposition 7.10 -- a budget-balanced VCG mechanism exists iff maximized welfare is a sum of functions of the others' types
-- statement:
--   In the dominant-strategy model of Chapter 7 with $N \ge 2$ agents, let $q$ be an efficient decision rule. Then there is an ex post budget-balanced VCG mechanism $(q, t_1, \dots, t_N)$ — transfers of VCG form with $\sum_i t_i(\theta) = 0$ for every $\theta$ — if and only if for every agent $i$ there is a function $f_i : \Theta_{-i} \to \mathbb R$ such that
--
--   $$
--   \sum_{i=1}^N u_i(q(\theta), \theta_i) = \sum_{i=1}^N f_i(\theta_{-i}) \qquad \text{for all } \theta \in \Theta .
--   $$
--
--   The maximized welfare, as a function of the type vector, must be a sum of functions each of which ignores one agent's type. In the bilateral trade model the maximized welfare $\max\{\theta_S, \theta_B\}$ has no such form, so no budget-balanced VCG mechanism exists there. The result is attributed to Holmström's 1977 thesis via Milgrom (2004, p.54).
--
--   **Formalization Note** The hypothesis $N \ge 2$ is added: the proof divides by $N - 1$, and with a single agent the "only if" direction fails (the VCG mechanism with $\tau_1 = 0$ is budget balanced, while $u_1(q(\theta_1), \theta_1)$ need not be constant).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.138, Proposition 7.10 (N ≥ 2 added; see Formalization Note)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.10 (p.138), after Holmström (1977) via Milgrom (2004): with at least
two agents, let `q` be efficient. A budget-balanced VCG mechanism with decision rule `q` exists
if and only if there are functions `fᵢ : Θ₋ᵢ → ℝ` with `∑ᵢ uᵢ(q(θ), θᵢ) = ∑ᵢ fᵢ(θ₋ᵢ)` for all
`θ ∈ Θ`. -/
theorem budget_balanced_vcg_iff {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (hN : 2 ≤ Fintype.card ι) (q : (∀ i, Θ i) → A)
    (hq : IsEfficient u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ,
        IsVCG u (⟨q, t⟩ : DirectMechanism Θ A) ∧ BudgetBalanced (⟨q, t⟩ : DirectMechanism Θ A)) ↔
      ∃ f : ∀ i, Others Θ i → ℝ, ∀ θ : ∀ j, Θ j,
        ∑ i, u i (q θ) (θ i) = ∑ i, f i (restrict θ i) := by sorry

end MechanismDesign.VCG
