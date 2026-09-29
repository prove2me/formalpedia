-- Prove2me | Theorems.Thm_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
-- name    : Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/6917d0b9-17a5-5cb2-b635-07f7a8af428b
-- title:
--   Lifting isomorphisms of f.g. projectives along a square-zero quotient
-- statement:
--   Let $R$ be a commutative ring and $I \subseteq R$ an ideal with $I^2 = \bot$, i.e. the square of $I$ is the zero ideal. Let $P_1$ and $P_2$ be additive commutative groups carrying $R$-module structures, each assumed projective and finitely generated over $R$ (all three types $R$, $P_1$, $P_2$ lying in a single universe $u$, as Lean's universe discipline requires here). Suppose given an isomorphism $e$ of $R/I$-modules between the base changes $(R/I) \otimes_R P_1$ and $(R/I) \otimes_R P_2$, the $R/I$-module structures being those coming from the left tensor factor. The conclusion is that the type of $R$-linear isomorphisms $P_1 \simeq_R P_2$ is nonempty; that is, $P_1$ and $P_2$ are isomorphic as $R$-modules. Note that the conclusion asserts mere existence of an isomorphism and makes no compatibility claim relating it to $e$ after base change.
--
--   This is the statement that finitely generated projective modules over a commutative ring are rigid along a square-zero thickening: isomorphism after reduction modulo a square-zero ideal already forces isomorphism over $R$. It is used in the scheme-theoretic form of this rigidity, [`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_pullback_squareZero`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_pullback_squareZero), concerning invertible modules whose pullback along a square-zero closed immersion is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

set_option autoImplicit false

open TensorProduct

theorem Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    Nonempty (P₁ ≃ₗ[R] P₂) := by sorry
