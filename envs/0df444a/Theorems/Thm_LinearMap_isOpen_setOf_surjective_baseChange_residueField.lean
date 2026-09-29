-- Prove2me | Theorems.Thm_LinearMap_isOpen_setOf_surjective_baseChange_residueField
-- name    : LinearMap.isOpen_setOf_surjective_baseChange_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c6e926df-1832-5184-b80a-dcf14dc772e0
-- title:
--   Fibrewise surjectivity is open when the cokernel is finitely generated
-- statement:
--   Let $A$ be a commutative ring, let $P$ and $Q$ be $A$-modules (each an additive commutative group with an $A$-module structure), and let $d \colon P \to_{A} Q$ be an $A$-linear map. Assume that the cokernel $Q / \operatorname{range} d$ is a finite, i.e. finitely generated, $A$-module. Then the subset of the prime spectrum of $A$ consisting of those primes $\mathfrak p$ for which the base-changed map $d \otimes_A \kappa(\mathfrak p) \colon \kappa(\mathfrak p) \otimes_A P \to \kappa(\mathfrak p) \otimes_A Q$ is surjective, where $\kappa(\mathfrak p)$ denotes the residue field of the prime ideal $\mathfrak p$ (the residue field of the localisation of $A$ at $\mathfrak p$, here as the residue field attached to the ideal $\mathfrak p$), is open in $\operatorname{Spec} A$ with its Zariski topology. Surjectivity is the set-theoretic surjectivity of the underlying function of the base-changed linear map, and no further hypotheses on $P$, $Q$ or $A$ are imposed.
--
--   This is the commutative-algebra form of the statement that the locus where the cokernel of a linear map vanishes after passing to the fibre is open, the relevant locus being exactly the complement of the support of $\operatorname{coker} d$. It is used for the openness of the locus where the first cohomology of a fibre vanishes for a family whose cohomology is computed by a two-term complex, and is cited by [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre) and by [`LinearMap.isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff`](thm.html#LinearMap.isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_isOpen_setOf_surjective_baseChange_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open TensorProduct

theorem LinearMap.isOpen_setOf_surjective_baseChange_residueField
    {A : Type u} [CommRing A] {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (d : P →ₗ[A] Q) [Module.Finite A (Q ⧸ LinearMap.range d)] :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} := by sorry
