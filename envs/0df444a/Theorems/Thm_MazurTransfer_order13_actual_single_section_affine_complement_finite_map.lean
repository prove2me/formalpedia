-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_single_section_affine_complement_finite_map
-- name    : MazurTransfer.order13_actual_single_section_affine_complement_finite_map
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T07:58:22.436356+00:00
-- url     : https://prove2.me/theorems/c7d3335e-a497-4d60-8d25-bfdeb09c17d2
-- title:
--   Actual positive-infinity complement is affine with a finite parameter map
-- statement:
--   Let $R$ be a noetherian integral domain with $104$ invertible. On the literal order-13 curve, set $t=y+x^3+x^2+1$, $p=xt$, $q=x(p+2)$ and $B=R[T][p,q]\subset A_{\rm ord}$ with $T\mapsto t$.
--
--   The actual complement $U$ of the positive infinity section $(z,w)=(0,1)$ is affine, and there is an isomorphism $\operatorname{Spec}B\simeq U$ compatible with the original ordinary chart inclusion. Under this isomorphism, the actual parameter map $\operatorname{Spec}B\to\mathbb A^1_R$ transports to a finite morphism $U\to\mathbb A^1_R$ over the original base map of the curve.
--
--   The open $U$ is explicitly the union of the ordinary chart and the reciprocal patch obtained by inverting $(w-1-z-z^3)(w-1-z+z^3)$. The theorem constructs the isomorphism from checked local comparisons and glues the literal chart morphisms. It assumes no supplied affine-complement identification or finite map. Full two-chart finite-map data, integral Picard compatibility, rational rank zero and Mazur's theorem remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned recovered reciprocal-coordinate, unit, universal-property and surjectivity proofs using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained. The unchanged public actual-curve geometric-integrality and flatness/smoothness results supply the coordinate-domain proofs; the actual overlap equivalence and faithful localizations prove injectivity. Complete owned gluing, overlap, exact-complement, isomorphism and finite-map transport proofs. The actual section-carrier alias is expanded definitionally to its underlying infinity morphism.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_single_section_affine_complement_finite_map.{u}
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
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
    let ε : ReciprocalRing R →+* R :=
      AdjoinRoot.lift (Polynomial.evalRingHom (0 : R)) (1 : R)
        (by simp [reciprocalEquation, reciprocalPolynomial, eval₂_pow, eval₂_C])
    let s : Spec (.of R) ⟶ curveScheme R :=
      Spec.map (CommRingCat.ofHom ε) ≫ reciprocalChartMap R
    let δ : ReciprocalRing R :=
      (wCoordinate R - 1 - zCoordinate R - zCoordinate R ^ 3) *
        (wCoordinate R - 1 - zCoordinate R + zCoordinate R ^ 3)
    let ℓ : Spec (.of (Localization.Away δ)) ⟶ reciprocalScheme R :=
      Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (Localization.Away δ)))
    letI : IsOpenImmersion ℓ := IsOpenImmersion.of_isLocalization δ
    let j : Spec (.of (Localization.Away δ)) ⟶ curveScheme R := ℓ ≫ reciprocalChartMap R
    letI : IsOpenImmersion j := IsOpenImmersion.comp ℓ (reciprocalChartMap R)
    let U : (curveScheme R).Opens := (ordinaryChartMap R).opensRange ⊔ j.opensRange
    IsAffineOpen U ∧ (U : Set (curveScheme R)) = (Set.range s)ᶜ ∧
      ∃ e : Spec (.of B) ≅ U.toScheme,
        Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ e.hom ≫ U.ι = ordinaryChartMap R ∧
        IsFinite (e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) B))) ∧
        (e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) B))) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
          U.ι ≫ curveToBase R := by sorry
