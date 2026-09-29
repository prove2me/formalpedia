-- Prove2me | Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
-- name    : IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ee205e9a-3d2a-5e5e-ad0e-bf078a4af350
-- title:
--   Simple transcendental extension is the rational function field
-- statement:
--   Let $K$ be a field, $L$ a field equipped with a $K$-algebra structure, and let $x \in L$ be transcendental over $K$ (that is, $x$ is not a root of any nonzero polynomial over $K$, in Mathlib's sense `Transcendental K x`). The assertion is the existence of an isomorphism of $K$-algebras $e$ from the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}` of $L/K$, viewed as a field in its own right via its coercion to a type, onto the field $\mathrm{RatFunc}\,K$ of rational functions in one variable over $K$, such that $e$ sends the canonical element of $K(x)$ given by $x$ together with the proof that $x$ lies in the adjunction to the indeterminate `RatFunc.X`. Thus the conclusion is not merely an abstract isomorphism $K(x) \cong K(X)$ but an isomorphism normalised so that the distinguished generator $x$ corresponds to $X$.
--
--   This is the standard fact that a simple transcendental extension $K(x)$ is $K$-isomorphic to the rational function field $K(X)$, in the form that tracks the generator $x \mapsto X$. It serves as the bridge allowing statements formulated over $\mathrm{RatFunc}\,K$ to be transported to subfields of a given field; it is used in the construction of models of modular curves, for instance in the unramifiedness arguments for polynomials over the relevant level rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
    (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] (x : L) (hx : Transcendental K x) :
    ∃ e : ↥(IntermediateField.adjoin K ({x} : Set L)) ≃ₐ[K] RatFunc K,
      e ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ = RatFunc.X := by sorry
