-- Prove2me | Theorems.Thm_MyersonBargaining_NashSolution_uniform_mechanism_bic
-- name    : MyersonBargaining.NashSolution.uniform_mechanism_bic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:09.505074+00:00
-- url     : https://prove2.me/theorems/987d373f-bb16-4c3b-a66c-f4688b5ece88
-- title:
--   Section 2 — the uniform mechanism is Bayesian incentive-compatible
-- statement:
--   Let $G$ be a finite Bayesian collective choice problem with nonempty choice set $C$. Consider the direct mechanism that selects each choice with the same probability, independently of the reported type profile:
--
--   $$
--   \pi(c\mid\alpha)=\frac{1}{|C|}\qquad(c\in C).
--   $$
--
--   This is a choice mechanism and is Bayesian incentive-compatible. It supplies a concrete mechanism in the incentive-feasible set used by Theorem 1.
--
--   **Formalization Note** The paper says only that the uniform mechanism "would be incentive-compatible"; the Lean statement makes both parts explicit: the constraints (2′) (nonnegativity and summing to one over $C$) and the inequalities (6). $C$ is nonempty, so $1/|C|$ is not a division by zero.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 65, proof of Theorem 1

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Proof of Theorem 1, p. 65: uniform random choice is incentive-compatible. -/
theorem uniform_mechanism_bic (G : Problem ι A C) :
    let π : C → (∀ i, A i) → ℝ := fun _ _ => 1 / (Fintype.card C : ℝ)
    IsChoiceMechanism π ∧ IsBIC G π := by sorry

end MyersonBargaining.NashSolution
