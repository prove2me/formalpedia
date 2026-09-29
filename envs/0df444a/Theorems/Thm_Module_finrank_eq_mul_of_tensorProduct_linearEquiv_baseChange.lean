-- Prove2me | Theorems.Thm_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
-- name    : Module.finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/15c5204e-24fd-50b2-b915-2f9e96314b9f
-- title:
--   Dimension of a faithfully flat algebra trivialised by base change
-- statement:
--   Let $\kappa$ be a field and let $B$, $C$, $D$ be types in one universe, with $B$ and $C$ commutative rings that are $\kappa$-algebras, $C$ a $B$-algebra in such a way that the $\kappa$-, $B$- and $C$-actions form a scalar tower $\kappa \to B \to C$, and $D$ an additive commutative group equipped with a $\kappa$-module structure. Assume $B$, $C$ and $D$ are finite (i.e. finitely generated) as $\kappa$-modules, and that $C$ is faithfully flat as a $B$-module. Assume further that there is an isomorphism of $C$-modules
--   $$e \colon C \otimes_B C \;\xrightarrow{\ \sim\ }\; C \otimes_\kappa D,$$
--   where in both tensor products $C$ acts through the left-hand factor. Then
--   $$\operatorname{finrank}_\kappa C = \operatorname{finrank}_\kappa D \cdot \operatorname{finrank}_\kappa B.$$
--   No multiplicativity or $B$-linearity of $e$ is assumed: only $C$-linearity enters, and $D$ carries no algebra structure, merely that of a finite-dimensional $\kappa$-vector space.
--
--   This is the coordinate-ring form of the statement that orders multiply along a torsor: for finite $\kappa$-schemes $\operatorname{Spec} C \to \operatorname{Spec} B$ and $\operatorname{Spec} D$, a trivialisation $\operatorname{Spec} C \times_{\operatorname{Spec} B} \operatorname{Spec} C \cong \operatorname{Spec} C \times_\kappa \operatorname{Spec} D$ over $\operatorname{Spec} C$ forces $\dim_\kappa C = \dim_\kappa D \cdot \dim_\kappa B$. It is used in the analysis of the special fibres of the Néron models attached to the modular curves $X_H$ and $X_0$, where the degree of a finite flat kernel group scheme is computed from such a trivialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Module.finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
    {κ : Type u} [Field κ] {B C D : Type u} [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    [Algebra B C] [IsScalarTower κ B C] [AddCommGroup D] [Module κ D]
    [Module.Finite κ B] [Module.Finite κ C] [Module.Finite κ D] [Module.FaithfullyFlat B C]
    (e : C ⊗[B] C ≃ₗ[C] C ⊗[κ] D) :
    Module.finrank κ C = Module.finrank κ D * Module.finrank κ B := by sorry
