-- Prove2me | Theorems.Thm_Hatcher_fundamentalGroup_map_injective_of_retraction
-- name    : Hatcher.fundamentalGroup_map_injective_of_retraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-14T12:43:02.913188+00:00
-- url     : https://prove2.me/theorems/2501351d-c317-4567-8a00-b0d5099d62b5
-- title:
--   Hatcher Proposition 1.17 — a retraction induces an injection on π₁
-- statement:
--   Suppose $X$ retracts onto $A$: there are maps $i \colon A \to X$ and $r \colon X \to A$ with $r \circ i = \mathrm{id}_A$. Then for every basepoint $a_0 \in A$ the induced homomorphism
--
--   $$i_* \colon \pi_1(A, a_0) \longrightarrow \pi_1\bigl(X, i(a_0)\bigr)$$
--
--   is injective.
--
--   **Role.** This is the simplest illustration of the fundamental group turning a statement about spaces into one about groups: a retraction forces an injection on $\pi_1$, so a space whose fundamental group cannot inject into that of $X$ cannot be a retract of it.
--
--   **Formalization note.** Hatcher states this for a subspace $A \subseteq X$ with $i$ the inclusion; the form here takes an arbitrary pair $i, r$ with $r \circ i = \mathrm{id}$, which specialises to that and is what the proof uses. Hatcher's proposition has a second clause — that $i_*$ is an *isomorphism* when $A$ is a deformation retract — which is **not** formalized here; only the injectivity clause is.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, Section 1.1, p. 36, Proposition 1.17, first clause: "If a space X retracts onto a subspace A, then the homomorphism i_* : pi_1(A, x0) -> pi_1(X, x0) induced by the inclusion i : A -> X is injective." PROVENANCE: the second clause of that proposition -- that i_* is an isomorphism when A is a deformation retract -- is NOT formalized in this statement; it is published separately. The retraction is taken as an arbitrary pair i, r with r . i = id, which specialises to Hatcher's subspace inclusion.

import Mathlib

namespace Hatcher

open ContinuousMap FundamentalGroup

theorem fundamentalGroup_map_injective_of_retraction {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) (r : C(X, A)) (hr : ∀ a, r (i a) = a) (a₀ : A) :
    Function.Injective (FundamentalGroup.map i a₀) := by
  sorry

end Hatcher
