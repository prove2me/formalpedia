-- Prove2me | Theorems.Thm_Module_Projective_exists_baseChange_quotient_iso_of_squareZero
-- name    : Module.Projective.exists_baseChange_quotient_iso_of_squareZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/27acbcbd-be8b-5114-9a24-598fc9a881b1
-- title:
--   Finite projective modules lift along a square-zero quotient
-- statement:
--   Let $R$ be a commutative ring (in a fixed universe $u$) and let $I \subseteq R$ be an ideal with $I^2 = \bot$, i.e. the square of $I$ is the zero ideal. Let $P$ be an abelian group equipped with a module structure over the quotient ring $R/I$, and assume that $P$ is projective and finitely generated as an $R/I$-module. The conclusion asserts the existence of a type $P'$ in the same universe $u$, together with an additive commutative group structure on $P'$ and an $R$-module structure on it, such that $P'$ is projective and finitely generated as an $R$-module, and such that the type of $R/I$-linear isomorphisms $(R/I) \otimes_R P' \simeq P$ is nonempty. Here the base change $(R/I) \otimes_R P'$ is the tensor product over $R$ of the $R$-algebra $R/I$ with $P'$, regarded as a module over $R/I$, and the isomorphism is required to be linear over $R/I$ (hence in particular over $R$). Thus every finitely generated projective module over $R/I$ is, up to isomorphism, the reduction of a finitely generated projective $R$-module.
--
--   This is the standard lifting statement for finitely generated projective modules along a square-zero (more generally nilpotent) ideal, obtained classically by lifting an idempotent matrix over $R/I$ to an idempotent matrix over $R$. It is used in the construction of rigidified line bundles over square-zero thickenings, applied to the charts of a cover by two affine opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Projective_exists_baseChange_quotient_iso_of_squareZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

set_option autoImplicit false

open TensorProduct

theorem Module.Projective.exists_baseChange_quotient_iso_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P : Type u) [AddCommGroup P] [Module (R ⧸ I) P]
    [Module.Projective (R ⧸ I) P] [Module.Finite (R ⧸ I) P] :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module R P'),
      Module.Projective R P' ∧ Module.Finite R P' ∧
      Nonempty (((R ⧸ I) ⊗[R] P') ≃ₗ[R ⧸ I] P) := by sorry
