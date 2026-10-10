-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_positive_infinity_section_complement
-- name    : MazurTransfer.order13_actual_positive_infinity_section_complement
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T07:19:53.680184+00:00
-- url     : https://prove2.me/theorems/80dec0a6-56e6-49a8-aeac-9b7dbe2f8178
-- title:
--   Actual positive infinity section: exact global open complement over every commutative ring
-- statement:
--   For every commutative ring $R$, consider the literal glued order-13 sextic curve $X_R$ with ordinary coordinates $(x,y)$ and reciprocal coordinates $(z,w)$. The positive infinity evaluation sends $z$ to zero and $w$ to one. Its composite with the reciprocal chart is an actual section $s_+$ of $X_R\to\operatorname{Spec}R$.
--
--   Set
--
--   $$\delta=(w-1-z-z^3)(w-1-z+z^3).$$
--
--   Localization defines an actual open immersion $j:\operatorname{Spec}(A_\infty[1/\delta])\to X_R$. Its image together with the entire ordinary chart is exactly the complement of the positive infinity section:
--
--   $$\operatorname{im}(X_{\mathrm{ord}}\to X_R)\cup\operatorname{im}(j)=X_R\setminus\operatorname{im}(s_+).$$
--
--   The reciprocal-chart evaluation is a closed immersion. No field, domain, characteristic, noetherianity, supplied model, affine-complement identification or Picard representation is assumed. The assertion identifies the exact global open needed for gluing the already constructed single-section finite coordinate algebra; that affine identification and the full finite-map package remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned section-evaluation, prime-ideal, two-chart gluing and global complement proofs; per-file attribution retained. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_positive_infinity_section_complement.{u}
    (R : Type u) [CommRing R] :
    let ε : ReciprocalRing R →+* R :=
      AdjoinRoot.lift (Polynomial.evalRingHom (0 : R)) (1 : R)
        (by simp [reciprocalEquation, reciprocalPolynomial, eval₂_pow, eval₂_C])
    let s : Spec (.of R) ⟶ curveScheme R :=
      Spec.map (CommRingCat.ofHom ε) ≫ reciprocalChartMap R
    let δ : ReciprocalRing R :=
      (wCoordinate R - 1 - zCoordinate R - zCoordinate R ^ 3) *
        (wCoordinate R - 1 - zCoordinate R + zCoordinate R ^ 3)
    let j : Spec (.of (Localization.Away δ)) ⟶ curveScheme R :=
      Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (Localization.Away δ))) ≫
        reciprocalChartMap R
    s ≫ curveToBase R = 𝟙 _ ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom ε)) ∧
      IsOpenImmersion j ∧
      Set.range (ordinaryChartMap R) ∪ Set.range j = (Set.range s)ᶜ := by sorry
