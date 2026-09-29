-- Prove2me | Theorems.Thm_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
-- name    : IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/fb8ab559-a876-591b-9fa4-9603a48ed6be
-- title:
--   Cofinality of finite levels over K above a finite level over ℚ
-- statement:
--   Let $q$ be a prime, let $K$ be an intermediate field of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$ (written `PadicAlgCl q`) that is finite-dimensional over $\mathbb{Q}_q$, and let $F$ be an intermediate field of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ over $\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$. The assertion is that there exists an intermediate field $E$ of $\overline{\mathbb{Q}}_q/K$ which is finite-dimensional over $K$ and has the following property: for every $K$-automorphism $\sigma$ of $\overline{\mathbb{Q}}_q$ lying in the fixing subgroup of $E$ (that is, $\sigma x = x$ for all $x \in E$), the image of $\sigma$ under the composite monoid homomorphism that first transports $\sigma$ through the inverse of `IntermediateField.fixingSubgroupEquiv K` into the fixing subgroup of $K$ inside $\overline{\mathbb{Q}}_q \simeq_{\mathbb{Q}_q} \overline{\mathbb{Q}}_q$, includes it into the full group $\overline{\mathbb{Q}}_q \simeq_{\mathbb{Q}_q} \overline{\mathbb{Q}}_q$, and then applies [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) — the homomorphism sending a $\mathbb{Q}_q$-automorphism to its restriction of scalars to $\mathbb{Q}$ followed by `AlgEquiv.restrictNormalHom` for the normal subextension $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ of $\overline{\mathbb{Q}}_q/\mathbb{Q}$ — lies in the fixing subgroup of $F$.
--
--   This is a cofinality statement for the two systems of finite levels: the finite subextensions of $\overline{\mathbb{Q}}_q/K$ are cofinal among the preimages, under the localisation map on Galois groups, of the fixing subgroups of finite subextensions of $\overline{\mathbb{Q}}/\mathbb{Q}$. It is used in the continuous group cohomology arguments over the local Galois group, where openness of subgroups and passage to a finite level must be checked.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
      ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup →
        ((localGaloisToGlobal q).comp
        (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) σ ∈ F.fixingSubgroup := by sorry
