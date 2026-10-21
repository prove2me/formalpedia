-- Prove2me | Theorems.Thm_NatureSLT_Consistency_finite_class_lln
-- name    : NatureSLT.Consistency.finite_class_lln
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:33.145493+00:00
-- url     : https://prove2.me/theorems/6c3e22da-517d-4462-b1c6-a7477b2c683f
-- title:
--   Section 2.3.1 — law of large numbers for a finite set of functions
-- statement:
--   Let $F$ be a probability measure on $Z$ and let $Q(z,\alpha)$, $\alpha\in\Lambda$, be a set of real functions with finitely many elements, each integrable with respect to $F$. For an i.i.d. sample $z_1,\dots,z_\ell$ from $F$ let
--
--   $$\xi^\ell = \sup_{\alpha\in\Lambda}\Bigl|\int Q(z,\alpha)\,dF(z) - \frac1\ell\sum_{i=1}^\ell Q(z_i,\alpha)\Bigr|.$$
--
--   Then $\xi^\ell$ converges to zero in probability:
--
--   $$\lim_{\ell\to\infty} P\{\xi^\ell > \varepsilon\} = 0 \qquad \forall\varepsilon>0.$$
--
--   This is the law of large numbers in an $N$-dimensional vector space, the base case of uniform two-sided convergence; the problem the chapter studies is what replaces it when $\Lambda$ is infinite.
--
--   **Formalization Note** "Contains a finite number $N$ of elements" is finiteness of the set of functions $\{Q(\cdot,\alpha):\alpha\in\Lambda\}$ (`(Set.range Q).Finite`); the parameter type $\Lambda$ itself may be infinite, as on the page, where only the set of functions is counted. Integrability of each $Q(\cdot,\alpha)$ is assumed so that its expectation exists. The supremum is taken in the extended reals; probabilities are values of the product measure $F^\ell$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 41, Section 2.3.1

import Mathlib
import Definitions.Def_NatureSLT_Consistency_risk
import Definitions.Def_NatureSLT_Consistency_uniformConvergence

open MeasureTheory Filter Topology

namespace NatureSLT.Consistency

/-- The law of large numbers for a finite set of functions (Vapnik 2000, Section 2.3.1, p. 41):
if the set of functions `Q(z, α)`, `α ∈ Λ`, contains a finite number `N` of elements (`hfin`:
the set `{Q(·, α) : α ∈ Λ}` of functions is finite; the parameter type `Λ` itself may be
infinite), the random variables `ξ^ℓ = sup_α |∫ Q(z, α) dF(z) − (1/ℓ) ∑ Q(zᵢ, α)|` (2.5)
converge in probability to zero, i.e. uniform two-sided convergence (2.6) holds. Each `Q(·, α)`
is assumed integrable, so that its expectation exists. -/
theorem finite_class_lln {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    [IsProbabilityMeasure F] (Q : Λ → Z → ℝ) (hfin : (Set.range Q).Finite)
    (hint : ∀ α, Integrable (Q α) F) :
    UniformTwoSidedConvergence F Q := by sorry

end NatureSLT.Consistency
