-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
-- name    : NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/ebc27418-c742-5d7b-bdce-90769988ae6e
-- title:
--   Infinite places of C^M have trivial decomposition group
-- statement:
--   Let $E$ and $C$ be number fields with $C$ an $E$-algebra and $C/E$ Galois, and let $M$ be a subgroup of $\mathrm{Gal}(C/E)$ subject to the following condition: for every ring homomorphism $\varphi : C \to \mathbb{C}$ and every $\sigma \in \mathrm{Gal}(C/E)$ such that $\varphi$ is conjugated by $\sigma$ in the sense of `NumberField.ComplexEmbedding.IsConj` (complex conjugation of $\varphi$ equals $\varphi \circ \sigma$), one has $\sigma \in M$. Assume moreover that the fixed field $C^M =$ `IntermediateField.fixedField M` is Galois over $E$. The conclusion is that for every infinite place $w$ of $C^M$ and every $g \in \mathrm{Gal}(C^M/E)$ lying in [`NumberField.InfPlaceDecomp.decomp E (IntermediateField.fixedField M) w`](def/NumberField_ArchimedeanIdeleModule.html#L23), which by definition is the stabiliser of $w$ for the natural action of $\mathrm{Gal}(C^M/E)$ on the infinite places of $C^M$, one has $g = 1$. Thus every infinite place of $C^M$ has trivial decomposition group over $E$.
--
--   This is the archimedean clause of the classical statement that, when $M$ contains all the complex conjugations of $C$, no infinite place of $E$ ramifies in $C^M$, equivalently all decomposition groups at infinity are trivial. It is used in the construction of auxiliary cyclic cyclotomic layers, being cited by [`NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp`](thm.html#NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem.lean

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
open NumberField

theorem NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
    (E C : Type) [Field E] [NumberField E] [Field C] [NumberField C] [Algebra E C] [IsGalois E C]
    (M : Subgroup (C ≃ₐ[E] C))
    (hM : ∀ (φ : C →+* ℂ) (σ : C ≃ₐ[E] C), NumberField.ComplexEmbedding.IsConj φ σ → σ ∈ M)
    [IsGalois E (IntermediateField.fixedField M)] :
    ∀ (w : InfinitePlace (IntermediateField.fixedField M)) (g : (IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)),
      g ∈ NumberField.InfPlaceDecomp.decomp E (IntermediateField.fixedField M) w → g = 1 := by sorry
