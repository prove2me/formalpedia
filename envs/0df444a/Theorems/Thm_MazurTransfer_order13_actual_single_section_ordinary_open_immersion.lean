-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_single_section_ordinary_open_immersion
-- name    : MazurTransfer.order13_actual_single_section_ordinary_open_immersion
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T07:31:16.250967+00:00
-- url     : https://prove2.me/theorems/26d285c6-4608-4967-ac38-4aec5b49afb6
-- title:
--   Actual ordinary chart is an open subscheme of the single-section finite coordinate model
-- statement:
--   Let $R$ be a commutative ring in which $2$ is invertible. On the ordinary chart of the literal order-13 curve, put
--
--   $$A_R=R[x,y]/(y^2-(x^6+2x^5+x^4+2x^3+6x^2+4x+1)),\quad t=y+x^3+x^2+1,$$
--
--   $$p=xt,\quad q=x(p+2),\quad B_R=R[T][p,q]\subseteq A_R,\quad T\mapsto t.$$
--
--   The morphism induced by this actual inclusion is an open immersion with exact image:
--
--   $$\operatorname{Spec}A_R\hookrightarrow\operatorname{Spec}B_R,\qquad\operatorname{im}=D_{B_R}(t)\cup D_{B_R}(p+2).$$
--
--   No field, domain, noetherianity, supplied isomorphism or affine-complement identification is assumed. This promotes the two ordinary localization comparisons to an actual scheme chart of the single-section finite coordinate model. Gluing its reciprocal chart and identifying the entire model with the curve minus the positive infinity section remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned coordinate epimorphism, spectrum monomorphism, localization-comparison and exact-image proofs. Per-file attribution retained. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve

theorem MazurTransfer.order13_actual_single_section_ordinary_open_immersion.{u}
    (R : Type u) [CommRing R] (h2 : IsUnit (2 : R)) :
    let τ : CoordinateRing R := yCoordinate R + (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1)
    let μ : CoordinateRing R := xCoordinate R * τ
    let ν : CoordinateRing R := xCoordinate R * (μ + 2)
    let α : Algebra (Polynomial R) (CoordinateRing R) := (aeval τ).toRingHom.toAlgebra
    letI : Algebra (Polynomial R) (CoordinateRing R) := α
    letI : SMul (Polynomial R) (CoordinateRing R) := α.toSMul
    letI : Module (Polynomial R) (CoordinateRing R) :=
      @Algebra.toModule (Polynomial R) (CoordinateRing R) _ _ α
    let B : Subalgebra (Polynomial R) (CoordinateRing R) :=
      Algebra.adjoin (Polynomial R) ({μ,ν} : Set (CoordinateRing R))
    let tB : B := algebraMap (Polynomial R) B X
    let pB : B := ⟨μ, Algebra.subset_adjoin (by simp)⟩
    let f : Spec (.of (CoordinateRing R)) ⟶ Spec (.of B) :=
      Spec.map (CommRingCat.ofHom B.val.toRingHom)
    IsOpenImmersion f ∧
      Set.range f = (PrimeSpectrum.basicOpen tB ⊔ PrimeSpectrum.basicOpen (pB + 2) :
        Set (PrimeSpectrum B)) := by sorry
