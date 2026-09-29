-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule
-- name    : ModularCurve.XHDRModelAtP.pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/8f6fcb3e-c7b0-5dfb-ba34-5cb5723dce85
-- title:
--   Degeneracy push-forwards as norm homomorphisms on ℚ̄-points
-- statement:
--   Fixed throughout are a prime $p$, a natural number $M \neq 0$ divisible by $p$ with $M/p \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of the $j$-invariant lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by the integral form-ratios of level $\mathrm{SL}_2(\mathbb{Z})$; these make the two-chart integral models `toBase p (ΓM M H) hj` and `toBase p (ΓN p M H hpM) hj` over $\operatorname{Spec}(R\,p)$ available. Further fixed is a datum $\mathfrak{X}$ of type `XHDRModelAtP p M H hpM hj`, the Deligne–Rapoport style integral model package at $p$ for $X_H(M)$; of its fields the statement uses the section $\mathfrak{X}.\varepsilon_{\inf}$ of the level-$M$ model, the curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ of the function field `xHFunctionFieldBar M H` together with the isomorphism $\mathfrak{X}.\mathrm{eeta}$ of its curve with the $\overline{\mathbb{Q}}$-fibre of the level-$M$ model, the morphism $\mathfrak{X}.\pi$ from the level-$M$ to the level-$\Gamma_N$ model over $\operatorname{Spec}(R\,p)$, the involution $\mathfrak{X}.w$ and the composite $\mathfrak{X}.\pi_w$. Properness of the level-$M$ and level-$(M/p)$ models and separatedness of both are assumed. Here `JH M H` denotes $\mathrm{Pic}^0$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, i.e. degree-zero divisors modulo principal ones, and `genPt p` is the $\overline{\mathbb{Q}}$-point of $\operatorname{Spec}(R\,p)$.
--
--   Level-$M$ Picard data. A designation $D$ of relative $\mathrm{Pic}^0$ for the level-$M$ model (a scheme $D.P$ over $\operatorname{Spec}(R\,p)$ with a zero section) and `hD`, asserting that $D$ represents, relative to the rigidifying section $\mathfrak{X}.\varepsilon_{\inf}$ and the condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero), the functor of rigidified line bundles: it provides a Poincaré rigidified bundle on the curve over $D.\mathrm{toBase}$ satisfying that condition, the universal property that every such rigidified bundle over a base $t$ is induced by a unique morphism over $\operatorname{Spec}(R\,p)$ to $D.\mathrm{toBase}$, and triviality of the pullback along the zero section.
--
--   Generic fibre at level $M$. The hypothesis `hDQ` is the same representability statement for the base change of the model to $\mathbb{Q}$, the base-changed section and the designation $D.\mathrm{baseChange}\,\mathbb{Q}$; `hPQ` asserts that its Poincaré bundle is isomorphic to the $\mathbb{Q}$-base change of the pullback of the Poincaré bundle of `hD` along the first projection. An Abel–Jacobi morphism `ajQ` over $\mathbb{Q}$ from the generic curve to $(D.\mathrm{baseChange}\,\mathbb{Q}).\mathrm{toBase}$ is given, subject to `hajQε`, that the base-changed cusp section composed with `ajQ` is the zero section, and `hajQ`, that for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the generic curve over $t$, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor cut out by $t$ followed by the cusp section.
--
--   Comparison of fibres and the $\overline{\mathbb{Q}}$-level Abel–Jacobi map at level $M$. A morphism `kQ` from the $\overline{\mathbb{Q}}$-fibre to the $\mathbb{Q}$-fibre of the level-$M$ model is given with `hkQ₁`, `hkQ₂` saying that it respects the projection to the curve and intertwines the projections to the bases with $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$. The morphism `ajbar` from $\mathfrak{X}.\mathrm{Meta}.C$ to $D.P$ is prescribed by `hajbar` as $\mathfrak{X}.\mathrm{eeta}$ followed by `kQ`, `ajQ` and the first projection, lies over the base by `hajbar_over`, and a $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ of $\mathfrak{X}.\mathrm{Meta}.C$ is given which maps to the cusp section (`hεbar`) and is sent by `ajbar` to the zero section (`hεbar_aj`).
--
--   Dictionary at level $M$. A bijection `pts` from `JH M H` to the $\overline{\mathbb{Q}}$-points of $D.\mathrm{toBase}$, additive for the relative group law attached to `hD` (`hpts_add`), and Abel–Jacobi normalised by `hpts_aj`: for all $\overline{\mathbb{Q}}$-points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ with $s$ lying over the cusp section, there is a degree-zero divisor $D_v$ equal to the difference of the places of $x$ and of $s$ (each with multiplicity one) whose class satisfies $\mathrm{pts}([D_v]) = x$ followed by `ajbar`.
--
--   Level-$(M/p)$ data. A designation $D_0$ for the level-$\Gamma_N$ model and `hD₀`, the corresponding representability statement with rigidifying section $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$. Degeneracy maps on function fields are given as integral $\overline{\mathbb{Q}}$-algebra homomorphisms $\alpha_H, \beta_H$ from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to `xHFunctionFieldBar M H` (integrality in `hαint`, `hβint`), together with a curve model $\mathrm{Meta}_0$ of the level-$(M/p)$ function field over $\overline{\mathbb{Q}}$, an isomorphism $\mathrm{eeta}_0$ of its curve with the $\overline{\mathbb{Q}}$-fibre of the level-$\Gamma_N$ model satisfying `heeta₀`, and two place pins: `hMeta₀π` states that if a $\overline{\mathbb{Q}}$-point $y_0$ of $\mathrm{Meta}_0$ has the same image in the curve as the image of a $\overline{\mathbb{Q}}$-point $y$ under $\mathfrak{X}.\pi$, then the place of $y_0$ is the restriction along $\alpha_H$ of the place of $y$, and `hMeta₀πw` states the same with $\mathfrak{X}.w$ followed by $\mathfrak{X}.\pi$ and restriction along $\beta_H$.
--
--   The push-forwards. A pair `degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM))` of additive homomorphisms is given, pinned on divisors by `hdeg0` and `hdeg1`: whenever a degree-zero divisor $D_w$ at level $M/p$ is the push-forward along $\alpha_H$ (respectively $\beta_H$) of a degree-zero divisor $D_v$ at level $M$, then $\mathrm{degPts}\,0\,[D_v] = [D_w]$ (respectively $\mathrm{degPts}\,1\,[D_v] = [D_w]$).
--
--   Generic fibre and dictionary at level $M/p$. The hypotheses `hDQ₀`, `hPQ₀`, `ajQ₀`, `hajQ₀ε`, `hajQ₀`, `kQ₀`, `hkQ₀₁`, `hkQ₀₂`, `ajbar₀`, `hajbar₀`, `hajbar₀_over`, $\bar\varepsilon_0$, `hεbar₀`, `hεbar₀_aj`, `pts₀`, `hpts₀_add`, `hpts₀_aj` are the exact analogues of the level-$M$ items above for the level-$\Gamma_N$ model, the designation $D_0$, the section $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$, the curve model $\mathrm{Meta}_0$ with $\mathrm{eeta}_0$, and the bijection `pts₀` from `JH (M / p) (infSubgroup p M H hpM)` to the $\overline{\mathbb{Q}}$-points of $D_0.\mathrm{toBase}$.
--
--   The degeneracy morphism $\pi$ and the norm classification. The morphism $\mathfrak{X}.\pi$ is assumed finite, flat and locally of finite presentation, with `hrk` asserting that its fibre rank at every point equals $p+1$. Finally $\delta : \mathrm{Fin}\,2 \to$ morphisms from $D.\mathrm{toBase}$ to $D_0.\mathrm{toBase}$ over $\operatorname{Spec}(R\,p)$ is given, subject to three conditions. `hδ₀`: for every scheme $T$, every $t : T \to \operatorname{Spec}(R\,p)$ and every $T$-point $a$ of $D.\mathrm{toBase}$, the pullback of the Poincaré bundle of `hD₀` along $a$ followed by $\delta\,0$ is isomorphic to the rigidification, along the section determined by $t$ and by $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$ (that is, tensoring with the pullback along the projection of the dual of the restriction to that section), of the norm module $\det_{p+1}$ of the push-forward along the base change of $\mathfrak{X}.\pi$ to $T$, in degree $p+1$, of the pullback of the Poincaré bundle of `hD` along $a$, tensored with the dual of the corresponding determinant of the push-forward of the unit. `hδ₁`: the same with the base change of $\mathfrak{X}.\pi_w$ in place of that of $\mathfrak{X}.\pi$. `hδmul`: for each $i \in \mathrm{Fin}\,2$, every $T$, $t$ and all $T$-points $x, y$ of $D.\mathrm{toBase}$, the composite of the product of $x$ and $y$ for the relative group law of `hD` with $\delta\,i$ equals the product, for the relative group law of `hD₀`, of the composites of $x$ and of $y$ with $\delta\,i$.
--
--   The conclusion is a single equation: for every $i \in \mathrm{Fin}\,2$ and every $x \in$ `JH M H`, the underlying morphism of the $\overline{\mathbb{Q}}$-point $\mathrm{pts}_0(\mathrm{degPts}\,i\,x)$ of $D_0.\mathrm{toBase}$ equals the underlying morphism of $\mathrm{pts}(x)$ followed by $\delta\,i$.
--
--   This identifies, on $\overline{\mathbb{Q}}$-points, the two morphisms $\delta_0, \delta_1$ between the relative $\mathrm{Pic}^0$ objects of the integral models at $p \mid M$ — characterised by taking the Poincaré bundle to the norm of relative degree $p+1$ along $\pi$, respectively along $w$ followed by $\pi$ — with the degeneracy push-forwards $\alpha_*, \beta_* : J_H(M) \to J_{H'}(M/p)$ defined on divisor classes. It is used by [`ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special`](thm.html#ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special), in the construction of the degeneracy homomorphisms needed for the analysis of the Jacobian at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

set_option maxHeartbeats 800000 in

theorem ModularCurve.XHDRModelAtP.pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    [IsProper (toBase p (ΓN p M H hpM) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hMeta₀π : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y))
    (hMeta₀πw : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y))
    (degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM)))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)

    (hDQ₀ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))) (D₀.baseChange ℚ))
    (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) ℚ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ₀ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (D₀.baseChange ℚ).toBase)
    (hajQ₀ε : (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1 ≫ ajQ₀.1 = (D₀.baseChange ℚ).zeroSection)
    (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)),
      Nonempty ((hDQ₀.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (t ≫ (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ₀ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ))
    (hkQ₀₁ : kQ₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p))
    (hkQ₀₂ : kQ₀ ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar₀ : Meta₀.C ⟶ D₀.P) (hajbar₀ : ajbar₀ = eeta₀ ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst D₀.toBase (specMap (R p) ℚ))
    (hajbar₀_over : ajbar₀ ≫ D₀.toBase = Meta₀.toBase ≫ genPt p)
    (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
    (hεbar₀ : εbar₀.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1)
    (hεbar₀_aj : εbar₀.1 ≫ ajbar₀ = genPt p ≫ D₀.zeroSection)

    (pts₀ : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) D₀.toBase)
    (hpts₀_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM),
      pts₀ (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (pts₀ x) (pts₀ y))
    (hpts₀_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
        (pts₀ (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀)
    [IsSeparated (toBase p (ΓM M H) hj)]

    [IsFinite 𝔛.π.1] [Flat 𝔛.π.1] [LocallyOfFinitePresentation 𝔛.π.1] (hrk : ∀ x, 𝔛.π.1.finrank x = p + 1)
    (δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓN p M H hpM) hj) t (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
            (pullback.snd (toBase p (ΓN p M H hpM) hj) t)
          (Scheme.Modules.normModule (curveChange 𝔛.π.1 𝔛.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓN p M H hpM) hj) t (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
            (pullback.snd (toBase p (ΓN p M H hpM) hj) t)
          (Scheme.Modules.normModule (curveChange 𝔛.πw.1 𝔛.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδmul : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) (δ i) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul t
          (NeronModelInfra.schemeHomOverComp x (δ i)) (NeronModelInfra.schemeHomOverComp y (δ i))) :
    ∀ (i : Fin 2) (x : JH M H), (pts₀ (degPts i x)).1 = (pts x).1 ≫ (δ i).1 := by sorry
