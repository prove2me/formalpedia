-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic
-- name    : ModularCurve.XHDRModelAtP.exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/ff961ebc-1bfe-5cb1-bed7-8a0dd9832361
-- title:
--   Level-M/p generic fibre and the two degeneracy embeddings
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$, with $M/p$ non-zero, and assume $j =$ `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms of full level. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which packages a proper flat integral model at level `ΓM M H` over $\operatorname{Spec} R_p$ with normal affine charts, a proper smooth model at level `XHDRLevel.ΓN p M H hpM`, a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ of the field $\overline{\mathbb{Q}}\cdot F_H(M) =$ `xHFunctionFieldBar M H` together with an isomorphism `𝔛.eeta` onto the base change to $\overline{\mathbb{Q}}$ of the level-$M$ model, compatible with the arithmetic Galois action and pinned on the finite chart, and further data including a morphism `𝔛.π` to the level-`ΓN` model and an automorphism `𝔛.w`. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{\mathbb{Q}}\cdot F_H(M)$ such that whenever $f$ in that field and $u$ in $\overline{\mathbb{Q}}\cdot F_{H'}(M/p) =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` (with $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$) have the same Laurent series, the Laurent series of $\theta f$ is obtained from that of $u$ by `qExpand` at $p$, i.e. by $q \mapsto q^p$; and assume that $\theta$ reads `𝔛.w` on places: for $\overline{\mathbb{Q}}$-points $y, y'$ of `𝔛.Meta.C` that are sections of `𝔛.Meta.toBase`, if $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, then the place of $y'$ is the translate of the place of $y$ by the semilinear automorphism attached to $\theta$. The conclusion asserts the existence of two $\overline{\mathbb{Q}}$-algebra maps $\alpha_H, \beta_H : \overline{\mathbb{Q}}\cdot F_{H'}(M/p) \to \overline{\mathbb{Q}}\cdot F_H(M)$, both integral as ring maps, such that $\alpha_H u$ has the same Laurent series as $u$ while the Laurent series of $\beta_H u$ is obtained from that of $u$ by $q \mapsto q^p$, and of a curve model $\mathrm{Meta}_0$ over $\overline{\mathbb{Q}}$ of $\overline{\mathbb{Q}}\cdot F_{H'}(M/p)$ together with an isomorphism $e_0$ from $\mathrm{Meta}_0.C$ to the pullback of the level-`ΓN` base morphism along $\operatorname{Spec}$ of $R_p \to \overline{\mathbb{Q}}$ satisfying $e_0$ followed by the second projection $= \mathrm{Meta}_0.\mathrm{toBase}$, with the following two place dictionaries: for sections $y$ of `𝔛.Meta.toBase` and $y_0$ of $\mathrm{Meta}_0.\mathrm{toBase}$, if $y_0$ followed by $e_0$ and the first projection equals $y$ followed by `𝔛.eeta`, the first projection and `𝔛.π.1`, then the place of $y_0$ is the place of $y$ restricted along $\alpha_H$ (pullback of the valuation subring along $\alpha_H$); and if instead the comparison is made with `𝔛.w.hom` inserted before `𝔛.π.1`, then the place of $y_0$ is the place of $y$ restricted along $\beta_H$.
--
--   This is the generic-fibre dictionary at a level exactly divisible by $p$: it produces the geometric generic fibre of the smooth level-$M/p$ model, the inclusion and $q \mapsto q^p$ embeddings of the corresponding modular function fields, and the reading of the degeneracy map and of its Atkin–Lehner twist on places as restrictions along those two embeddings. It feeds the construction of the level data and relative Picard dictionary for the Néron object attached to such a model, [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve.XHDRLevel
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral),

      (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      ∃ (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
        (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
        (_ : IsIso eeta₀),

        eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
          y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
          Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y)) ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
          y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
          Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y)) := by sorry
