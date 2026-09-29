-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le
-- name    : ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/325c38c6-574f-5e64-a4fa-a3419c1289d5
-- title:
--   Relative Pic⁰ of the X_H(M) model at p
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, i.e. every unit $u$ with `ZMod.unitsMap` image $1$ lies in $H$. Assume the Laurent series `jqModC ℚ` lies in the full-level $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`: a proper, flat, integral, locally finitely presented and normal two-chart integral model `toBase p (ΓM M H) hj` of the level-$\Gamma_H(M)$ curve over the discrete valuation ring `R p`, together with the curve model `𝔛.Meta` of its geometric generic fibre over $\overline{\mathbb{Q}}$, the identification `𝔛.eeta` of that curve with the base change, and the further data and compatibilities packaged in that structure. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H` such that whenever $f$ in that field and $u$ in `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` have equal Laurent series, the Laurent series of $\theta f$ is `qExpand` at $p$ applied to that of $u$ (the substitution $q \mapsto q^p$). Assume moreover that for all $\overline{\mathbb{Q}}$-points $y, y'$ of `𝔛.Meta.C` over the base, if $y'$ followed by `𝔛.eeta`, the first projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, then the place `𝔛.Meta.pointEquivPlace y'` is the translate of `𝔛.Meta.pointEquivPlace y` by the semilinear automorphism `SemilinearAut.ofAlgAut θ`. Then there exists a `RelativePic0Designation` $D$ for this model over `R p` — a scheme $D.P$ with a structure morphism $D$.`toBase` to $\operatorname{Spec}($`R p`$)$ and a zero section — which represents the subfunctor of the rigidified relative Picard functor of the model with its section `𝔛.εinf` cut out by `algEquivZeroCut`, namely by the condition that a rigidified line bundle be algebraically equivalent to zero on every geometric fibre: there is a Poincaré bundle over $D$.`toBase` satisfying this condition, universal for it, and trivial along the zero section. Furthermore $D$.`toBase` is smooth, separated, quasi-compact, surjective and geometrically connected.
--
--   This is the representability of the relative $\mathrm{Pic}^0$ (the Jacobian) of the Deligne–Rapoport-style model of $X_H(M)$ over $\mathbb{Z}_{(p)}$ in the case $p \parallel M$, with $H$ containing the kernel of reduction modulo $M/p$, where the special fibre is a union of two smooth curves glued along supersingular points. It supplies the Jacobian scheme, together with its smoothness and geometric connectedness over the base, used in the construction of the Néron-model data attached to $J_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open AlgebraicGeometry.RelPicard
open AlgebraicCurve

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj),
      Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase ∧
        Surjective D.toBase ∧ GeometricallyConnected D.toBase := by sorry
