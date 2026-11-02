-- Prove2me | Theorems.Thm_FriedmannCunningham_policy_pivot
-- name    : FriedmannCunningham.policy_pivot
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T05:12:13.12656+00:00
-- url     : https://prove2.me/theorems/d536c42c-5bec-493c-82fe-cd1d2d19769e
-- title:
--   Lemma 11 and policy-pivot correspondence
-- statement:
--   For every n≥3 and every Boolean policy, the LP objective at its basic solution equals the sum of its decision-state values. At every decision vertex an improving alternative action is exactly an eligible positive-reduced-cost entering column, and the policy update is a genuine minimum-ratio simplex pivot.
-- source:
--   Avis and Friedmann (2017), Lemma 11 and §§4.2–4.3. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

open scoped BigOperators

/-- The §4.2–4.3 correspondence, including Lemma 11's objective identity. -/
theorem policy_pivot (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    FriedmannSimplex.basicObjective (program n) (policyBasis n hn σ) =
      (∑ r : Fin (rows n), policyValue n hn σ r) ∧
    ∀ r,
      (mdpImproving n hn σ r ↔
        FriedmannSimplex.improving (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))) ∧
      (mdpImproving n hn σ r →
        FriedmannSimplex.pivot (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))
          (policyBasis n hn (Function.update σ r (!σ r)))) := by sorry

end FriedmannCunningham
