-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
-- name    : ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/79bb6afa-ef6a-554b-95a7-a0ad41a5da83
-- title:
--   Inertia-fixed number field whose integers reduce onto 𝔽_{q²}
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, let $k$ be a field of characteristic $q$, and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Let $S$ be a finite subset of $k$ each of whose elements $a$ satisfies $a^{q^2} = a$. Then there exists an intermediate field $K_0$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, with the following two properties. First, every $\sigma$ in the subgroup `A.inertiaSubgroupIn ℚ` of $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ — that is, in the image of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup of $A$ into the full automorphism group — fixes $K_0$ pointwise: $\sigma x = x$ for all $x \in K_0$. Second, every $a \in S$ lies in the range of `NodeLocalized.redRestrict red K₀`, the homomorphism $A \cap K_0 \to k$ obtained by restricting $\mathrm{red}$ along the inclusion of the subring $A \cap K_0$ of $\overline{\mathbb Q}$ (intersection of $A$ with $K_0$) into $A$; equivalently, each $a \in S$ is $\mathrm{red}(x)$ for some $x \in A$ lying in $K_0$.
--
--   This is the Teichmüller-lift statement in the form needed for descent of a node: the $q^2$-th power-fixed elements of the residue field are realised by elements of an unramified-at-$q$ number field, so that coefficients read off from the residue field can be lifted to a field on which inertia acts trivially. It is used in the node-descent and place-specialisation steps, where prolongation tuples and node packages over such a field $K_0$ are constructed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] [CharP k q] (red : A →+* k)
    (S : Finset k) (hS : ∀ a ∈ S, a ^ (q ^ 2) = a) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₀),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ K₀, σ x = x) ∧
      ∀ a ∈ S, a ∈ Set.range (NodeLocalized.redRestrict red K₀) := by sorry
