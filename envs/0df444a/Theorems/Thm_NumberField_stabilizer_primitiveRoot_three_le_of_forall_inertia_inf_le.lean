-- Prove2me | Theorems.Thm_NumberField_stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le
-- name    : NumberField.stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/68531c14-cd05-5363-b628-8a28e016eb39
-- title:
--   Subgroups containing all ℚ(ζ₃)-inertia contain Stab(ζ₃)
-- statement:
--   Let $L$ be a number field which is Galois over $\mathbb{Q}$, and let $\zeta \in L$ be a primitive cube root of unity, i.e. $\zeta$ satisfies `IsPrimitiveRoot ζ 3`. Let $H$ be a subgroup of the Galois group $L \simeq_{\mathbb{Q}} L$ of $\mathbb{Q}$-algebra automorphisms of $L$, and consider the natural action of this group on $L$, whose stabiliser subgroup `MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ` of $\zeta$ is the subgroup of automorphisms fixing $\zeta$, that is, $\mathrm{Gal}(L/\mathbb{Q}(\zeta))$. Assume that for every maximal ideal $P$ of the ring of integers $\mathcal{O}_L$ the intersection of the inertia subgroup of $P$ inside $L \simeq_{\mathbb{Q}} L$ with the stabiliser of $\zeta$ is contained in $H$. The conclusion is that the whole stabiliser of $\zeta$ is contained in $H$: a subgroup of $\mathrm{Gal}(L/\mathbb{Q})$ which absorbs the $\mathbb{Q}(\zeta)$-inertia at every finite place already contains $\mathrm{Gal}(L/\mathbb{Q}(\zeta))$. The hypothesis ranges over all maximal ideals, including those above $3$.
--
--   This is the finite-level relative Hermite–Minkowski statement for the base field $\mathbb{Q}(\zeta_3)$: it expresses that $\mathbb{Q}(\zeta_3)$ admits no nontrivial everywhere-unramified extension, in the group-theoretic form needed for Galois-cohomological arguments, and it rests on the vanishing of nontrivial unramified extensions recorded in [`NumberField.finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt`](thm.html#NumberField.finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt). It is used to derive the corresponding statement over an algebraic closure, [`AlgebraicClosure.stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le`](thm.html#AlgebraicClosure.stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le), which in turn feeds the $p = 3$ case of the vanishing of a certain Ext group in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le.lean

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField

theorem NumberField.stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (H : Subgroup (L ≃ₐ[ℚ] L))
    (hH : ∀ P : Ideal (NumberField.RingOfIntegers L), P.IsMaximal →
      P.inertia (L ≃ₐ[ℚ] L) ⊓ MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ ≤ H) :
    MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ ≤ H := by sorry
