-- Prove2me | Theorems.Thm_MetricTesting_Characterization_testing_removal_equivalence
-- name    : MetricTesting.Characterization.testing_removal_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:11.465643+00:00
-- url     : https://prove2.me/theorems/2b3fd131-b8b1-4075-9ed2-d6ddaf30bbcf
-- title:
--   Theorem 3.4 — Testing-removal equivalence
-- statement:
--   Fix the standing local matrix framework with nonempty valid targets, and assume the predicate $\Phi$ is measurable in the inherited product Borel spaces. For every $\epsilon>0$, positivity of the removal modulus gives a one-sided $\epsilon$-tester, uniformly over all positive orders, with query bound
--   $$\binom k2\left\lceil\frac{\log3}{\rho(\epsilon)}\right\rceil.$$
--   When $\rho(\epsilon)=+\infty$, there are no $\epsilon$-far inputs and the bound is zero.
--
--   Conversely, if the family is extendable and has a one-sided $q$-query $\epsilon$-tester, put $r=\max\{k,2q\}$. The literal canonical inspection rule, querying a uniform induced $r$-submatrix and rejecting iff it is invalid, is a one-sided tester with at most $\binom r2$ queries. If $n<r$, it queries the whole matrix. In addition,
--   $$\rho(\epsilon)\ge\frac{2}{3\binom rk}.$$
--   Consequently, under extendability,
--   $$\Phi\text{ removable}\quad\Longleftrightarrow\quad\mathcal P\text{ one-sided testable}.$$
--   All three clauses are retained, including the precise bounds and the order-independent quantification. The forward clause requires no extendability. This theorem connects an operational testing model with a purely extremal density modulus.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
--   - encoding: randomized adaptive decision trees with exact real answers → measurable seed-and-history rules and absorbing-stop recursive transcripts; reason: the seed is input independent, queries may repeat, all positive matrix orders are allowed, and no computability or precision condition is added
--   - encoding: infima over violation densities and minima over valid repairs → ENNReal infima with empty infimum +infinity, and attained minima of natural discrepancy counts; reason: the nonempty valid targets make the finite range of discrepancy counts attain its least element; empty far-input and packing classes retain the source convention
--   - encoding: a uniform r-set and successive uniform unused images → a uniform injection Fin r into Fin n, used in first-touch order; reason: each r-set has exactly r! enumerations; revealing their positions sequentially gives precisely the source conditional sampling law
--   - encoding: the unqualified measurability assumption on Φ → measurability in the finite product of the inherited Borel spaces on Λ; reason: this fixes the usual product-measurability convention without assuming that Λ is Borel, closed, bounded, or countable
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 10, Theorem 3.4 (PDF p. 11)

import Definitions.Def_MetricTesting_Characterization_moduli
import Definitions.Def_MetricTesting_Characterization_sampling

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Theorem 3.4, printed p.10 / PDF p.11: the forward bound, the
canonical converse with full inspection below r, the modulus bound, and
the final qualitative equivalence, each with its own structural assumptions. -/
theorem testing_removal_equivalence (F : LocalData) (hP : TargetsNonempty F)
    (hmeas : PredicateMeasurable F) (ε : ℝ) (hε : 0 < ε) :
    (0 < removalModulus F ε → HasTester F ε (removalQueryBound F ε)) ∧
    (Extendable F → ∀ q : ℕ, HasTester F ε q →
      CanonicalTesters F ε (max F.k (2*q)) ∧
      ENNReal.ofReal (2 / (3 * (Nat.choose (max F.k (2*q)) F.k : ℝ))) ≤
        removalModulus F ε) ∧
    (Extendable F → (Removable F ↔ OneSidedTestable F)) := by sorry

end MetricTesting.Characterization
