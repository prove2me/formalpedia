-- Prove2me | Theorems.Thm_FriedmannCunningham_mdp_valid
-- name    : FriedmannCunningham.mdp_valid
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T05:11:45.268819+00:00
-- url     : https://prove2.me/theorems/fe0aa63b-6b91-408b-8744-02cf8539ebee
-- title:
--   Lemma 8 — absorbing decision-process model
-- statement:
--   For every n≥3 each collapsed action has nonnegative transition probabilities whose sum is at most one, and every policy transient system has nonzero determinant. This is the eliminated-state algebraic prerequisite supplied by the source’s absorbing-chain construction.
-- source:
--   Avis and Friedmann (2017), Figure 7 and Lemma 8, §3.2. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

open scoped BigOperators

/-- Figure 7 and Lemma 8, after eliminating the random vertices: each action's
transition row is substochastic and every policy's transient matrix is invertible. -/
theorem mdp_valid (n : ℕ) (hn : 3 ≤ n) :
    (∀ r b q, 0 ≤ transition n hn r b q) ∧
    (∀ r b, (∑ q : Fin (rows n), transition n hn r b q) ≤ 1) ∧
    (∀ σ : Policy n,
      (FriedmannSimplex.basisMatrix (program n) (policyBasis n hn σ)).det ≠ 0) := by sorry

end FriedmannCunningham
