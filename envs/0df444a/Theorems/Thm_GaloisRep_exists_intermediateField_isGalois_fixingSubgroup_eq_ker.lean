-- Prove2me | Theorems.Thm_GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker
-- name    : GaloisRep.exists_intermediateField_isGalois_fixingSubgroup_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d71a337d-d00f-53db-a6d5-542866900574
-- title:
--   Kernel field of a Galois representation with open kernel
-- statement:
--   Let $G$ be a finite group and let $\rho \colon \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to G$ be a group homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $G$. Suppose given an intermediate field $M$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$ and whose fixing subgroup, i.e. the subgroup of automorphisms acting as the identity on $M$, is contained in $\ker \rho$. The conclusion asserts the existence of an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$, is Galois over $\mathbb{Q}$, whose fixing subgroup is exactly $\ker \rho$, and whose degree $[F : \mathbb{Q}]$ (as `Module.finrank ℚ F`) divides the cardinality of $G$. Note that only divisibility of $|G|$ by $[F:\mathbb{Q}]$ is asserted, not the sharper identity $[F:\mathbb{Q}] = |\operatorname{im} \rho|$ that the proof in fact establishes along the way.
--
--   This is the construction of the field cut out by a Galois representation with open kernel, a standard consequence of Krull's infinite Galois theory: the fixed field of $\ker\rho$ is the finite Galois extension whose Galois group is the image of $\rho$. It is used in the exclusion of irreducible two-dimensional mod $3$ representations with prescribed ramification, where a representation is converted into a finite Galois number field of controlled degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.exists_intermediateField_isGalois_fixingSubgroup_eq_ker
    {G : Type*} [Group G] [Finite G] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      F.fixingSubgroup = ρ.ker ∧ Module.finrank ℚ F ∣ Nat.card G := by sorry
