-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
-- name    : ModularCurve.XHDRModelAtP.comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/a80e6fc7-bb39-5ded-a7d5-aeec6163bc7a
-- title:
--   Factorisation of the pulled-back point ideal on the generic fibre
-- statement:
--   Fix a prime $p$, a nonzero level $M$ with $p \mid M$ and $M/p \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a proof $hj$ that the $q$-series $j$ lies in the level-one $q$-expansion function field over $\mathbb{Q}$. Let $\mathfrak{X}$ be an element of `XHDRModelAtP p M H hpM hj`, so in particular it carries the two-chart integral models at levels $\Gamma_M(H)$ and $\Gamma_N$ over `R p`, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field $\mathtt{xHFunctionFieldBar}\,M\,H$, an isomorphism $\mathfrak{X}.\mathrm{eeta}$ of its underlying scheme with the base change of the level-$\Gamma_M(H)$ model to $\overline{\mathbb{Q}}$ compatible with the structure maps, and a degeneracy morphism $\mathfrak{X}.\pi$ from the level-$\Gamma_M(H)$ model to the level-$\Gamma_N$ model over `R p`. Let $\alpha_H$ be an $\overline{\mathbb{Q}}$-algebra map from $\mathtt{xHFunctionFieldBar}\,(M/p)\,(\mathtt{infSubgroup}\,p\,M\,H\,hpM)$ to $\mathtt{xHFunctionFieldBar}\,M\,H$ which is the identity on underlying Laurent series ($h\alpha$) and is integral ($h\alpha\mathrm{int}$). Let $\mathrm{Meta}_0$ be a curve model of the smaller function field over $\overline{\mathbb{Q}}$, together with an isomorphism $e_0$ onto the base change of the level-$\Gamma_N$ model compatible with the structure maps, the hypothesis that the preimage of the finite chart is nonempty, and the pinning $hpin_0$: for every $a$ in the finite chart algebra at level $\Gamma_N$, the germ of $a$ at the generic point corresponds under $\mathrm{Meta}_0.\mathrm{ffEquiv}^{-1}$ to the Laurent series obtained from the $q$-expansion of $a$ by coefficient extension $\mathtt{coeffEmb}$. Assume further that both structure maps to `Spec (R p)` are separated, that both barred function fields are curves over $\overline{\mathbb{Q}}$ (principal divisors, finite residue extensions, free rank-one Kähler module) and essentially of finite type, and that the base change of $\mathfrak{X}.\pi$ to $\overline{\mathbb{Q}}$ via `curveChange` is finite, flat and locally of finite presentation. Finally let $y$ be a section of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ over $\overline{\mathbb{Q}}$ whose associated place $\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}\,y$ has ramification index $1$ along $\alpha_H$, and let $y' : \mathrm{Fin}\,k \to$ sections be injective, with $y'_j \neq y$, all $y'_j$ having places restricting along $\alpha_H$ to the restriction of the place of $y$, every place of the larger field with that restriction and distinct from the place of $y$ being the place of some $y'_j$, and $e_j$ the ramification index along $\alpha_H$ of the place of $y'_j$. The conclusion has two parts: first, each $y'_j$ and $y$ have the same image in the level-$\Gamma_N$ model under the composite with $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.\pi$; second, the ideal sheaf of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to that common image point at level $\Gamma_N$, pulled back (`comap`) along the base change of $\mathfrak{X}.\pi$, equals the ideal of the divisor of $y$ at level $\Gamma_M(H)$ multiplied by the product over $j$ of the ideals of the divisors of the $y'_j$ raised to the power $e_j$.
--
--   This is the scheme-theoretic dictionary on the geometric generic fibre of the degeneracy map between the integral models at levels $\Gamma_M(H)$ and $\Gamma_N$: places above a given place, counted with their ramification indices along $\alpha_H$, account exactly for the multiplicities in the pullback of the point ideal. It feeds [`ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow`](thm.html#ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow), where the existence of the auxiliary sections $y'_j$ is supplied, and rests on the curve-model statement [`AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex`](thm.html#AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex) together with the identification of generic points with places given by the pinning hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hαint : αH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hne₀ : Nonempty (Scheme.Opens.toScheme ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))))
    (hpin₀ : haveI := hne₀
      ∀ a : ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj),
            ((Meta₀.ffEquiv.symm
                (Meta₀.C.germToFunctionField
                  ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))
                  (((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                    (((ιFin p (XHDRLevel.ΓN p M H hpM) hj).appIso ⊤).inv
                      ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj))).inv a))))
                : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
              coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓN p M H hpM))) : LaurentSeries ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)] [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]

    [IsFinite (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]
    [Flat (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]
    [LocallyOfFinitePresentation (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hw₀ : Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace y) = 1)
    (k : ℕ) (y' : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (e : Fin k → ℕ)
    (hinj : Function.Injective y') (hne : ∀ j, y' j ≠ y)
    (hfib : ∀ j, (𝔛.Meta.pointEquivPlace (y' j)).restrictAlong αH hαint = (𝔛.Meta.pointEquivPlace y).restrictAlong αH hαint)
    (hall : ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      w.restrictAlong αH hαint = (𝔛.Meta.pointEquivPlace y).restrictAlong αH hαint → w ≠ 𝔛.Meta.pointEquivPlace y →
        ∃ j, w = 𝔛.Meta.pointEquivPlace (y' j))
    (he : ∀ j, e j = Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace (y' j))) :

    (∀ j, (y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) ∧

    (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) ((y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ 𝔛.π.1)
        (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
        (by rw [Category.assoc, 𝔛.π.2, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
              ← Category.assoc, y.2, Category.id_comp])).I.comap
        (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) =
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
          (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
          (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp])).I *
        ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ((y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
            (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
            (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, (y' j).2,
                  Category.id_comp])).I ^ (e j) := by sorry
