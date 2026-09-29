-- Prove2me | Theorems.Thm_Hatcher_fundamentalGroup_map_bijective_of_retraction_homotopic_id
-- name    : Hatcher.fundamentalGroup_map_bijective_of_retraction_homotopic_id
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-14T12:43:01.218325+00:00
-- url     : https://prove2.me/theorems/5aea07b6-4d53-4b65-a788-d777500f21c4
-- title:
--   Hatcher Proposition 1.17, second clause — a retraction whose other composite is homotopic to the identity induces a bijection on π₁
-- statement:
--   Suppose $X$ retracts onto $A$ — there are $i \colon A \to X$ and $r \colon X \to A$ with $r \circ i = \mathrm{id}_A$ — and suppose in addition that $i \circ r$ is homotopic to $\mathrm{id}_X$. Then for every $a_0 \in A$ the induced homomorphism
--
--   $$i_* \colon \pi_1(A, a_0) \longrightarrow \pi_1\bigl(X, i(a_0)\bigr)$$
--
--   is bijective, not merely injective.
--
--   **Role.** This is the second clause of Hatcher's Proposition 1.17, the case in which the retraction is a deformation retraction. Together with the first clause it is the standard tool for computing a fundamental group by retracting a space onto a simpler subspace.
--
--   **Formalization note.** The hypothesis is stated as the two conditions the conclusion actually uses, rather than through a named notion of deformation retract, which Mathlib does not have. It is accordingly **weaker** than Hatcher's: he requires the deforming homotopy to fix $A$ pointwise at every time, which is not needed here, so this statement implies his clause rather than matching it. Bijectivity of the homomorphism stands in for being an isomorphism.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, Section 1.1, p. 36, Proposition 1.17, second clause: "If A is a deformation retract of X, then i_* is an isomorphism." PROVENANCE: the hypothesis here is weaker than Hatcher's. He requires a deformation retraction, whose homotopy fixes A pointwise at every time; this statement assumes only r . i = id and that i . r is freely homotopic to the identity, which is what the conclusion uses. It therefore implies Hatcher's clause rather than matching it.

import Mathlib

namespace Hatcher

open ContinuousMap FundamentalGroup

theorem fundamentalGroup_map_bijective_of_retraction_homotopic_id {A X : Type*}
    [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (r : C(X, A))
    (hr : ∀ a, r (i a) = a) (H : (i.comp r).Homotopic (ContinuousMap.id X)) (a₀ : A) :
    Function.Bijective (FundamentalGroup.map i a₀) := by
  sorry

end Hatcher
