-- Prove2me | Theorems.Thm_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
-- name    : IsLocalRing.exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/8cc5ff3c-cf7a-577d-aeed-b387cb939a5c
-- title:
--   Small kernels as finite residue-field vector spaces
-- statement:
--   Let $B$ and $B_1$ be commutative rings in a fixed universe, with $B$ local and Artinian, and let $\pi \colon B \to B_1$ be a ring homomorphism whose kernel $I = \ker \pi$ satisfies $I \cdot \mathfrak m = 0$, where $\mathfrak m =$ `maximalIdeal B`; the product here is the product of ideals of $B$, so the hypothesis says exactly that $\mathfrak m$ annihilates $I$. The conclusion asserts the existence of a type $V$ in the same universe, carried together with the following structures on it: an additive commutative group structure, a module structure over the residue field $k =$ `ResidueField B` making $V$ a finite $k$-module, a $B$-module structure compatible with the $k$-structure via $B \to k$ (a scalar tower), a $k^{\mathrm{op}}$-module structure, and the assertion that the left and right $k$-actions agree; and, finally, a $B$-linear map $\iota \colon V \to B$ which is injective and whose range, as a $B$-submodule of $B$, equals $I$ viewed as a $B$-submodule by restriction of scalars along the identity.
--
--   This is the standard observation, used throughout deformation theory of Artin rings, that the kernel of a small extension of an Artinian local ring is a finite-dimensional vector space over the residue field. The universe-polymorphic formulation with an explicit ring homomorphism $\pi$ is what allows it to be applied in the lifting arguments for smoothness, group laws and bare deformations over Artinian bases that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

universe u

theorem IsLocalRing.exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
    {B B₁ : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁] (π : B →+* B₁)
    (hsmall : RingHom.ker π * maximalIdeal B = ⊥) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ResidueField B) V) (_ : Module.Finite (ResidueField B) V)
      (_ : Module B V) (_ : IsScalarTower B (ResidueField B) V)
      (_ : Module (ResidueField B)ᵐᵒᵖ V) (_ : IsCentralScalar (ResidueField B) V) (ι : V →ₗ[B] B),
      Function.Injective ι ∧ LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker π) := by sorry
