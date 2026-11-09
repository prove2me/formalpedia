-- Prove2me | Theorems.Thm_MetricTesting_Characterization_testing_structure_equivalence
-- name    : MetricTesting.Characterization.testing_structure_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:45.222361+00:00
-- url     : https://prove2.me/theorems/3653f722-834d-4ca1-8450-500d4609ccd6
-- title:
--   Corollary 3.11 — Testing-structure equivalence
-- statement:
--   Fix an integer $k\ge2$, a nonempty value set $\Lambda\subseteq\mathbb R_{\ge0}$, and a permutation-invariant measurable $k$-point predicate $\Phi$. Its associated local matrix family $\mathcal P$ consists of the arrays whose every $k$-point restriction satisfies $\Phi$. Assume nonempty valid targets at every order $n\ge k$ and extendability. The following three assertions are equivalent:
--   $$\begin{aligned}
--   &\forall\epsilon>0\ \exists q\in\mathbb N\ \forall n\ge1:\ \mathcal P_n\text{ admits a one-sided }q\text{-query }\epsilon\text{-tester};\\
--   &\forall\epsilon>0:\ \rho(\epsilon)>0;\\
--   &\Gamma(\theta)\longrightarrow0\ (\theta\downarrow0)\quad\text{and}\quad\forall\alpha>0:\ \Delta(\alpha)>0.
--   \end{aligned}$$
--   Testers are information-theoretic and adaptive, use exact values, accept valid inputs with probability one, and reject every input at distance strictly greater than $\epsilon$ with probability at least $2/3$. The query cap may depend on the predicate and $\epsilon$ but not on $n$. The value set may be uncountable, unbounded, or nonclosed. The theorem preserves all three conditions and both directions, identifying exactly the structural content of one-sided constant-query testability.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
--   - encoding: randomized adaptive decision trees with exact real answers → measurable seed-and-history rules and absorbing-stop recursive transcripts; reason: the seed is input independent, queries may repeat, all positive matrix orders are allowed, and no computability or precision condition is added
--   - encoding: infima over violation densities and minima over valid repairs → ENNReal infima with empty infimum +infinity, and attained minima of natural discrepancy counts; reason: the nonempty valid targets make the finite range of discrepancy counts attain its least element; empty far-input and packing classes retain the source convention
--   - encoding: Γ(θ) tends to zero as θ decreases to zero → for every η > 0 there is θ > 0 with Γ(θ) ≤ η; reason: Γ is nonnegative and nondecreasing on nonnegative θ, making this exactly the source right-limit condition
--   - encoding: the unqualified measurability assumption on Φ → measurability in the finite product of the inherited Borel spaces on Λ; reason: this fixes the usual product-measurability convention without adding regularity of Λ
--   - encoding: three equivalent assertions → the conjunction of the first iff second and the second iff third; reason: these two equivalences assert precisely the full three-way equivalence
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), pp. 11–12, Corollary 3.11 (PDF pp. 12–13)

import Definitions.Def_MetricTesting_Characterization_moduli
import Definitions.Def_MetricTesting_Characterization_decision_tree

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Corollary 3.11, printed pp.11–12 / PDF pp.12–13.
Three-way equivalence, retaining all three assertions in full. -/
theorem testing_structure_equivalence (F : LocalData) (hP : TargetsNonempty F)
    (hext : Extendable F) (hmeas : PredicateMeasurable F) :
    (OneSidedTestable F ↔ Removable F) ∧
      (Removable F ↔ CompletionStable F ∧ PackingAmplification F) := by sorry

end MetricTesting.Characterization
