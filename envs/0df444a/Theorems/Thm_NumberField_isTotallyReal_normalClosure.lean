-- Prove2me | Theorems.Thm_NumberField_isTotallyReal_normalClosure
-- name    : NumberField.isTotallyReal_normalClosure
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-09T23:50:48.60076+00:00
-- url     : https://prove2.me/theorems/ec2ee8bb-6fbc-4832-9825-0c47ce689f16
-- title:
--   The normal closure of a totally real number field is totally real
-- statement:
--   Let $\mathbb{F}$ be a totally real number field, that is, one all of whose infinite places are real. Then its normal closure over $\mathbb{Q}$, taken inside a fixed algebraic closure, is again totally real.
--
--   Write $\widetilde{\mathbb{F}}$ for that normal closure. Concretely
--
--   $$\widetilde{\mathbb{F}} \;=\; \bigvee_{\sigma} \sigma(\mathbb{F}),$$
--
--   the compositum taken over all $\mathbb{Q}$-embeddings $\sigma$ of $\mathbb{F}$ into the algebraic closure. Each $\sigma$ is injective, so $\sigma(\mathbb{F})$ is isomorphic to $\mathbb{F}$ as a field and is therefore totally real; and a subfield is totally real precisely when it is contained in the maximal real subfield of the ambient field, a containment preserved under suprema. Hence the compositum is totally real.
--
--   Equivalently: once a field is normal over $\mathbb{Q}$, all of its complex embeddings share a common image, so having one real embedding already forces every embedding to be real. Total reality is thus inherited by normal closures, which is what allows a question about arbitrary totally real fields to be reduced to the Galois case — the reduction used for Leopoldt's conjecture, where the general totally real statement follows from the Galois one together with the propagation of a positive Leopoldt defect along finite extensions.
--
--   **Formalization note.** `IsTotallyReal` is Mathlib's predicate that every infinite place is real, and `normalClosure ℚ F (AlgebraicClosure F)` is Mathlib's normal closure, defined as the supremum of the ranges of the $\mathbb{Q}$-algebra maps into the algebraic closure. Mathlib carries the totally real predicate for `Subfield`s and the normal closure as an `IntermediateField`, so the proof passes between the two.
-- source:
--   Standard field theory; not currently in Mathlib. Used to reduce Leopoldt's conjecture for totally real fields (Leopoldt.leopoldt_totallyReal) to its Galois case (Leopoldt.leopoldt_totallyReal_galois).

import Mathlib

open NumberField IntermediateField

namespace NumberField
theorem isTotallyReal_normalClosure (F : Type*) [Field F] [NumberField F]
    [IsTotallyReal F] :
    IsTotallyReal (normalClosure ℚ F (AlgebraicClosure F)) := by sorry
end NumberField
