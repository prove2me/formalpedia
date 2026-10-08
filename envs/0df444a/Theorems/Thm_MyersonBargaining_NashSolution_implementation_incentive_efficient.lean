-- Prove2me | Theorems.Thm_MyersonBargaining_NashSolution_implementation_incentive_efficient
-- name    : MyersonBargaining.NashSolution.implementation_incentive_efficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:36.716982+00:00
-- url     : https://prove2.me/theorems/744a2e51-a27d-4416-9d30-93add1d5ed9b
-- title:
--   Section 5 — an implementation of a bargaining solution is incentive-efficient
-- statement:
--   Fix a Bayesian collective choice problem and a conflict choice $c^*$. Suppose a Bayesian incentive-compatible choice mechanism $\pi$ generates a bargaining solution, meaning that its interim vector $V(\pi)$ maximizes the generalized Nash product over $F^*_+$. Then $\pi$ is incentive-efficient:
--
--   $$
--   \nexists\pi'\text{ Bayesian incentive-compatible choice mechanism such that }
--   V_{i,a_i}(\pi)<V_{i,a_i}(\pi')\quad\forall i,a_i.
--   $$
--
--   The claim concerns every implementing mechanism; it does not assert that the mechanism realizing the unique payoff vector is itself unique.
--
--   **Formalization Note** "Implementation" is read as: $\pi$ is a choice mechanism satisfying (2′) and (6), and $V(\pi)$ maximizes (18) over $F^*_+$. The statement does not assume Theorem 3's hypothesis, as the paper's paragraph does not; it holds for any conflict choice $c^*$.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 69, final paragraph of Section 5

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Section 5, p. 69: an implementation of a bargaining solution is incentive-efficient. -/
theorem implementation_incentive_efficient
    (G : Problem ι A C) (cstar : C) (π : C → (∀ i, A i) → ℝ)
    (hπ : IsChoiceMechanism π ∧ IsBIC G π)
    (hx : IsBargainingSolution G cstar (V G π)) :
    IsIncentiveEfficient G π := by sorry

end MyersonBargaining.NashSolution
