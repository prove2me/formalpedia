-- Prove2me | Theorems.Thm_IsOpen_exists_numberField_ker_restrictNormalHom_le
-- name    : IsOpen.exists_numberField_ker_restrictNormalHom_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/1ea48235-4e6c-59a9-b37a-5d3b8a981bae
-- title:
--   Open subgroups of Gal(ℚ̄/ℚ) contain a finite-level kernel
-- statement:
--   Let $H$ be a subgroup of the group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and assume that the underlying set of $H$ is open (the topology on the automorphism group being the Krull topology carried by Mathlib's instance). Then there exist a type $F$ together with a field structure on it, a `NumberField` structure (that is, $F$ is of characteristic zero and finite-dimensional over $\mathbb{Q}$), the property that $F/\mathbb{Q}$ is Galois, an algebra structure of $F$ on `AlgebraicClosure ℚ`, and the compatibility of this structure with the $\mathbb{Q}$-algebra structures (`IsScalarTower ℚ F (AlgebraicClosure ℚ)`), such that the kernel of the restriction homomorphism $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to \mathrm{Aut}_{\mathbb{Q}}(F)$, `AlgEquiv.restrictNormalHom F`, is contained in $H$. Thus every open subgroup of the absolute Galois group of $\mathbb{Q}$ contains the subgroup of automorphisms acting trivially on some number field $F$ that is Galois over $\mathbb{Q}$ and embedded in $\overline{\mathbb{Q}}$.
--
--   This is the standard translation, in infinite Galois theory for the Krull topology, between openness of a subgroup and factorisation through a finite Galois level. It provides the finite-level datum used by the Čebotarev- and Frobenius-density arguments of the project, and is cited by [`FreyPackage.eigenformRealizationSupplyFieldAtFamily`](thm.html#FreyPackage.eigenformRealizationSupplyFieldAtFamily), [`ModularCurve.exists_injective_linearMap_range_inf_eq_bot_of_baseChange_equiv_of_ne_top`](thm.html#ModularCurve.exists_injective_linearMap_range_inf_eq_bot_of_baseChange_equiv_of_ne_top) and [`Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`](thm.html#Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsOpen_exists_numberField_ker_restrictNormalHom_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsOpen.exists_numberField_ker_restrictNormalHom_le
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
      (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H := by sorry
