-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_weak_implies_strong
-- name    : OAI.PureTypeSystem.weak_implies_strong
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:12.278593+00:00
-- url     : https://prove2.me/theorems/3f976547-ddc2-4cd4-a816-4deec4f14682
-- statement:
--   The theorem states that for every type S of sorts and every pure type system specification P on S, which consists of an arbitrary axiom relation between pairs of sorts and an arbitrary ternary rule relation on sorts, with no functionality assumed for either, if the system is weakly normalizing then it is strongly normalizing. The terms are fully annotated de Bruijn lambda terms built from variables, sorts, applications, lambda abstractions and Pi types, with domain annotations on both binders. System-wide weak normalization means that for every valid context Γ (a list of types, each typable as a sort in the preceding context) and every legal term M, meaning M has some type or is itself the type of some term in Γ, M can be beta-reduced in finitely many steps to a beta-normal form. Beta reduction is the contextual closure, including inside binder domains and Pi domains and bodies, of contracting a redex (λA.b) a to b with a substituted. System-wide strong normalization means that for every valid context and legal term M, the term M is accessible for the converse of beta reduction, so no infinite beta-reduction sequence starts from M, including reductions inside all type annotations.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TypeSystemNormalization.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TypeSystemNormalization.lean; bytes 4166..4463
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TypeSystemNormalization

namespace OAI

namespace PureTypeSystem

universe u

/-- System-wide weak normalization implies strong normalization for every PTS,
including arbitrary sort types, nonfunctional rules and annotated terms. -/
theorem weak_implies_strong {S : Type u} (P : Specification S)
    (h : SystemWeaklyNormalizing P) : SystemStronglyNormalizing P := by
  sorry

end PureTypeSystem
end OAI
