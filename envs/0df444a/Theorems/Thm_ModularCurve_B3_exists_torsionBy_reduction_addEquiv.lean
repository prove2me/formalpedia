-- Prove2me | Theorems.Thm_ModularCurve_B3_exists_torsionBy_reduction_addEquiv
-- name    : ModularCurve.B3.exists_torsionBy_reduction_addEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/44aabecf-b500-5bf4-98da-9a12f52e3217
-- title:
--   Reduction is an isomorphism on p-torsion
-- statement:
--   Let $W$ be a Weierstrass curve over the field $H$ of the Tate-point construction, assumed elliptic, and let `specialFibre W` be the Weierstrass curve over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` whose coefficients are the coefficients at $0$ of $a_1,a_2,a_3,a_4,a_6$ of $W$, also assumed elliptic. Assume `IntegralCoeffs W`, i.e. each of $a_1,a_2,a_3,a_4,a_6$ has $\mathrm{orderTop} \ge 0$, and assume $\mathrm{orderTop}(\Delta_W) = 0$. Let $p$ be a prime. Then there is an isomorphism of additive groups $e$ from the $\mathbb{Z}$-torsion submodule $\{P : p \cdot P = 0\}$ of the affine point group of $W$ onto the corresponding $p$-torsion submodule of the affine point group of `specialFibre W`, which is given on coordinates by taking coefficients at $0$: for every $p$-torsion point $P$ and all $x, y \in H$ with $(x,y)$ nonsingular on the affine model of $W$, if $P$ is the affine point $(x,y)$, then $(x.\mathrm{coeff}\ 0, y.\mathrm{coeff}\ 0)$ is nonsingular on the affine model of `specialFibre W` and $e(P)$ is the affine point with these coordinates. Only the existence of such an $e$ is asserted, not uniqueness.
--
--   This is the good-reduction statement that reduction modulo the maximal ideal is injective, indeed bijective, on $p$-torsion for a model with integral coefficients and unit discriminant, together with the description of the reduction map on affine coordinates as passage to constant terms. It serves the construction of Tate points on modular curves, where the $p$-torsion of a curve over the Hahn-series field has to be identified with the $p$-torsion of its special fibre compatibly with coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_B3_exists_torsionBy_reduction_addEquiv.lean

import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint
open scoped Classical

theorem ModularCurve.B3.exists_torsionBy_reduction_addEquiv (W : WeierstrassCurve H)
    [W.IsElliptic] (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0)
    [(specialFibre W).IsElliptic] (p : ℕ) [Fact p.Prime] :
    ∃ e : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ) ≃+
        Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ),
      ∀ (P : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ)) (x y : H)
        (h : W.toAffine.Nonsingular x y),
        (P : W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x y h →
          ∃ h₀ : (specialFibre W).toAffine.Nonsingular (x.coeff 0) (y.coeff 0),
            ((e P : Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ)) :
                (specialFibre W).toAffine.Point) =
              WeierstrassCurve.Affine.Point.some (x.coeff 0) (y.coeff 0) h₀ := by sorry
