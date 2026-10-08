-- Prove2me | Theorems.Thm_OAI_Thomason_main
-- name    : OAI.Thomason.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.453338+00:00
-- url     : https://prove2.me/theorems/8bbf3940-1f9d-4e11-9b55-d30795e925c1
-- statement:
--   The theorem states that the proposition FullMain holds at universe level u, namely a conjunction of three claims about omega-categories (globular cells with source and target maps in every dimension, partial compositions along each dimension satisfying unit, associativity and interchange laws, and every cell having finite dimension) and the Street nerve. Write sd for Kan's subdivision functor, ex for its right adjoint, and take weak equivalences of simplicial sets to be maps whose geometric realization induces a bijection on connected components and on all homotopy groups at every basepoint, fibrations to be maps with the right lifting property against the horn inclusions, and cofibrations to be monomorphisms. The Thomason left functor from simplicial sets to omega-categories is the composite of two subdivisions followed by categorification (the colimit-preserving extension of the oriental cosimplicial object), and its right adjoint, the Thomason right functor, is the Street nerve followed by two applications of ex. First, the theorem asserts that there exists a model category structure on simplicial sets whose weak equivalences, fibrations and cofibrations are exactly these Kan-Quillen classes. Second, it asserts that there exists an exact model endpoint on omega-categories for this adjunction: a model structure whose weak equivalences and fibrations are the maps sent by the Thomason right functor to simplicial weak equivalences and Kan-Quillen fibrations, and whose cofibrations are those having the left lifting property against maps that are both; the fibrations are the maps with the right lifting property against the images of the horn inclusions, and the trivial fibrations those with it against the images of the boundary inclusions; both factorization systems are weak factorization systems; the category is complete, cocomplete and locally presentable; the model structure is left and right proper; the left functor sends monomorphisms to cofibrations, and trivial cofibrations when the monomorphism is a weak equivalence; and for any simplicial set K and any fibrant object Y, a map from the left functor of K to Y is a weak equivalence exactly when its adjunct is a simplicial weak equivalence. Third, for every n ≥ 1 the same endpoint structure is asserted to exist on the category of n-categories (omega-categories whose cells all equal their n-source), using the truncated left and right Thomason functors and their adjunction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThomasonModelStructures.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThomasonModelStructures.lean; bytes 135763..135826
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ThomasonModelStructures

noncomputable section

universe u v w

attribute [instance] OAI.Thomason.DirectedComplex.group

section

namespace OAI

theorem Thomason.main : OAI.Thomason.FullMain.{u} := by
  sorry

end OAI
end
end
