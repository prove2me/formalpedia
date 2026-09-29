-- Prove2me | Theorems.Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
-- name    : IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/1e63ea9c-8be2-5c4f-a0e9-a22e075fa315
-- title:
--   Global level subgroups are cofinal over a finite q-adic level
-- statement:
--   Let $q$ be a prime and write $\Omega$ for the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$. Let $K$ be an intermediate field of $\Omega/\mathbb{Q}_q$ that is finite-dimensional over $\mathbb{Q}_q$, and let $E$ be an intermediate field of $\Omega/K$ that is finite-dimensional over $K$. Then there exists an intermediate field $F$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with the following property: for every $K$-algebra automorphism $\sigma$ of $\Omega$, consider the image of $\sigma$ under the composite monoid homomorphism which first transports $\sigma$ along the inverse of `IntermediateField.fixingSubgroupEquiv K` into the subgroup of $\mathbb{Q}_q$-automorphisms of $\Omega$ fixing $K$ pointwise, includes this into $\Omega \simeq_{\mathbb{Q}_q} \Omega$, and then applies [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41), namely restriction of scalars to $\mathbb{Q}$ followed by `AlgEquiv.restrictNormalHom` to $\mathrm{AlgebraicClosure}\ \mathbb{Q}$; if that image lies in the fixing subgroup of $F$ in $\mathrm{Gal}(\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q})$, then $\sigma$ lies in the fixing subgroup of $E$, i.e. $\sigma$ fixes $E$ pointwise.
--
--   This is the cofinality statement needed to compare the topology on $\mathrm{Gal}(\Omega/K)$ given by subgroups pulled back from finite global levels $F/\mathbb{Q}$ with the topology given by finite local extensions $E/K$: every basic neighbourhood of the identity coming from a finite $E/K$ contains the preimage of some global level subgroup. It is used by the continuous-cohomology and roots-of-unity level arguments that run over a fixed finite $q$-adic level $K$, for instance in the analysis of coboundaries and of openness hypotheses for the associated cocycle maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q,
        ((localGaloisToGlobal q).comp
        (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup := by sorry
