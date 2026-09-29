-- Prove2me | Theorems.Thm_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
-- name    : GlobalGaloisRep.IsUnramifiedAt.algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/da51cbc2-6304-5344-b5cc-d32880871810
-- title:
--   Unramifiedness at q transfers from places to primes of 𝒪_F
-- statement:
--   Let $G$ be a group and let $\rho\colon(\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}})\to G$ be a group homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ`, and let $q$ be a natural number. Assume $q$ is prime and that $\rho$ is unramified at $q$ in the sense of [`GlobalGaloisRep.IsUnramifiedAt`](def/GaloisRep_GlobalUnramifiedAt.html#L9): for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ (the pushforward of `A.inertiaSubgroup ℚ` along the inclusion of the decomposition subgroup of $A$) is contained in $\ker\rho$. Let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is finite-dimensional and Galois over $\mathbb{Q}$, and assume $\ker\rho\le$ `F.fixingSubgroup`, i.e. every element of $\ker\rho$ fixes $F$ pointwise. Let $P$ be a maximal ideal of the ring of integers $\mathcal{O}_F$ containing the image of $q$. Then `Algebra.IsUnramifiedAt ℤ P` holds, that is, $\mathcal{O}_F$ is unramified over $\mathbb{Z}$ at $P$.
--
--   This is the passage from unramifiedness of a global Galois representation at $q$, formulated through inertia subgroups of valuation subrings of $\overline{\mathbb{Q}}$, to the classical statement that the primes above $q$ in a finite Galois subextension cut out by the kernel are unramified over $\mathbb{Z}$. It is used in the analysis of the conductor and discriminant bounds, via [`IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup`](thm.html#IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup), and in the irreducibility argument [`GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar`](thm.html#GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalGaloisRep.IsUnramifiedAt.algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
    {G : Type*} [Group G] {ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G} {q : ℕ}
    (hq : q.Prime) (hunr : GlobalGaloisRep.IsUnramifiedAt ρ q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : ρ.ker ≤ F.fixingSubgroup)
    (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal] (hqP : (q : NumberField.RingOfIntegers F) ∈ P) :
    Algebra.IsUnramifiedAt ℤ P := by sorry
