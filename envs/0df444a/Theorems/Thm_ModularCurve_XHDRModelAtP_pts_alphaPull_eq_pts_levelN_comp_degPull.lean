-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_pts_alphaPull_eq_pts_levelN_comp_degPull
-- name    : ModularCurve.XHDRModelAtP.pts_alphaPull_eq_pts_levelN_comp_degPull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f483a797-8308-5cfb-927a-64a078b0df56
-- title:
--   Degeneracy pull-backs match the point dictionaries
-- statement:
--   Throughout, $p$ is a prime, $M$ a non-zero natural number with $p \mid M$ and $p^2 \nmid M$, and $H$ a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`, phrased through `ZMod.unitsMap` for the divisibility $(M/p) \mid M$); $M/p$ is non-zero, and `infSubgroup p M H hpM` denotes the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. The hypothesis `hj` asserts that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-one $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`. Here `JH M H` is the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the geometric function field `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, and likewise `JH (M / p) (infSubgroup p M H hpM)` at level $M/p$.
--
--   The datum $\mathfrak{X}$ is a term of the structure `XHDRModelAtP p M H hpM hj`: integral-model data for the level-$\Gamma_M$ and level-$\Gamma_N$ curves over the base ring `R p`, comprising in particular a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ of `xHFunctionFieldBar M H`, an isomorphism `𝔛.eeta` of `𝔛.Meta.C` with the $\overline{\mathbb{Q}}$-fibre of `toBase p (ΓM M H) hj`, the cusp section `𝔛.εinf` of that model, an automorphism `𝔛.w` of its total space, and morphisms `𝔛.π` and `𝔛.πw` over `Spec (R p)` from the level-$\Gamma_M$ model to the level-$\Gamma_N$ model. The model `toBase p (ΓM M H) hj` is assumed proper.
--
--   *The $q$-expansion automorphism and its geometric pin.* $\theta$ is a $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H`, and `hθ` requires that whenever $f$ in that field and $u$ in `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` have the same underlying Laurent series, the Laurent series of $\theta f$ is `qExpand (AlgebraicClosure ℚ) p` applied to that of $u$, i.e. $\theta$ acts on the smaller field by $q \mapsto q^p$ on exponents. The hypothesis `hwgen` pins $\theta$ geometrically: for $\overline{\mathbb{Q}}$-points $y, y'$ of `𝔛.Meta.C` over its base, if the image of $y'$ in the integral model followed by `𝔛.w.hom` coincides with the image of $y$, then `𝔛.Meta.pointEquivPlace y'` equals `SemilinearAut.ofAlgAut θ` acting on `𝔛.Meta.pointEquivPlace y`.
--
--   *The level-$M$ Picard data.* $D$ is a `RelativePic0Designation` for `toBase p (ΓM M H) hj`, that is, a scheme `D.P` with a structure morphism `D.toBase` to `Spec (R p)` and a zero section; `hD` asserts that $D$ represents the relative sub-Picard functor cut out by `algEquivZeroCut`, whose condition is fibrewise algebraic equivalence to zero, with respect to the rigidifying section `𝔛.εinf`: it supplies a Poincaré bundle `hD.poincare` satisfying that condition, the universal property that every such `𝔛.εinf`-rigidified line bundle on a base $T \to \operatorname{Spec}(R p)$ is the pullback of `hD.poincare` along a unique $T$-point of `D.toBase`, and the normalisation that the pullback along the zero section is the unit bundle. The morphism `D.toBase` is assumed smooth (`hsm`), separated (`hsep`), quasi-compact (`hqc`), surjective (`hsurj`) and geometrically connected (`hgc`). Over the generic fibre, `hDQ` asserts that `D.baseChange ℚ` represents the corresponding functor for `baseChange (R p) (toBase p (ΓM M H) hj) ℚ` rigidified along `sectionBaseChange ℚ 𝔛.εinf`, and `hPQ` that its Poincaré bundle is isomorphic to the base change to $\mathbb{Q}$ of `hD.poincare` pulled back along the first projection of `pullback D.toBase (specMap (R p) ℚ)`.
--
--   *The Abel–Jacobi block at level $M$.* `ajQ` is a morphism from the generic fibre of the model to `(D.baseChange ℚ).toBase` over $\mathbb{Q}$ with `hajQε` saying that the base-changed cusp section followed by `ajQ` is the zero section, and `hajQ` its classifying property: for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the generic fibre over $t$, the pullback of `hDQ.poincare` along $x$ followed by `ajQ` has underlying module isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the cusp point $t$ followed by `sectionBaseChange ℚ 𝔛.εinf`. The morphism `kQ` compares the $\overline{\mathbb{Q}}$-fibre with the $\mathbb{Q}$-fibre of the model, `hkQ₁` and `hkQ₂` requiring compatibility with the first projection and with the second projection up to $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$. The morphism `ajbar : 𝔛.Meta.C ⟶ D.P` is required by `hajbar` to be `𝔛.eeta` followed by `kQ`, by `ajQ` and by the first projection, and by `hajbar_over` to lie over `𝔛.Meta.toBase` followed by `genPt p`. The point `εbar` is a $\overline{\mathbb{Q}}$-point of `𝔛.Meta.C` over its base lying above the cusp section (`hεbar`) and sent by `ajbar` to the zero section (`hεbar_aj`).
--
--   *The dictionary at level $M$.* `pts` is a bijection of `JH M H` with the $\overline{\mathbb{Q}}$-points of `D.toBase` over `genPt p`; `hpts_add` states that it carries addition to the relative group law attached to `hD` through `algEquivZeroGroupCut`, `hpts_galois` that for $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ one has $\mathrm{pts}(\sigma \cdot x) = \operatorname{Spec}(\sigma)$ followed by $\mathrm{pts}(x)$, and `hpts_aj` the Abel–Jacobi pin: for $\overline{\mathbb{Q}}$-points $x, s$ of `𝔛.Meta.C` with $s$ lying above the cusp section, there is a degree-zero divisor $D_v$ equal to $\mathrm{single}(\text{place of } x) - \mathrm{single}(\text{place of } s)$ whose class satisfies $\mathrm{pts}(\mathrm{Pic}^0(D_v)) = x$ followed by `ajbar`.
--
--   *The level-$M/p$ side.* The model `toBase p (ΓN p M H hpM) hj` is assumed proper and separated. A valuation-ring block is assumed: a valuation subring $A$ of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, that is, $p$ lies in the non-units of $A$, whose residue field has characteristic $p$ and is algebraically closed, together with a ring map $\rho : R p \to A$ with `hρ` saying that $\rho$ followed by the inclusion of $A$ is the structure map $R p \to \overline{\mathbb{Q}}$. Then $D_0$ is a `RelativePic0Designation` for `toBase p (ΓN p M H hpM) hj`, and `hD₀` asserts that it represents the same kind of fibrewise-algebraically-trivial rigidified Picard functor, rigidified along the section obtained by composing `𝔛.εinf` with `𝔛.π`.
--
--   *The degeneracy maps on function fields and places.* $\alpha_H, \beta_H$ are $\overline{\mathbb{Q}}$-algebra maps from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to `xHFunctionFieldBar M H`, integral by `hαint`, `hβint`. `Meta₀` is a curve model over $\overline{\mathbb{Q}}$ of the smaller function field, `eeta₀` an isomorphism of `Meta₀.C` with the $\overline{\mathbb{Q}}$-fibre of the level-$\Gamma_N$ model, compatible with the structure morphisms by `heeta₀`. The place pins `hMeta₀π` and `hMeta₀πw` state that if a $\overline{\mathbb{Q}}$-point $y_0$ of `Meta₀.C` is the image of a $\overline{\mathbb{Q}}$-point $y$ of `𝔛.Meta.C` under `𝔛.π` (respectively under `𝔛.w.hom` followed by `𝔛.π`), then `Meta₀.pointEquivPlace y₀` is the restriction along $\alpha_H$ (respectively along $\beta_H$) of `𝔛.Meta.pointEquivPlace y`. The family `degPts : Fin 2 → (JH M H →+ JH (M / p) …)` is pinned on divisor classes by `hdeg0` and `hdeg1`: `degPts 0` (respectively `degPts 1`) sends the class of a degree-zero divisor $D_v$ to the class of any degree-zero divisor equal to the pushforward of $D_v$ along $\alpha_H$ (respectively along $\beta_H$).
--
--   *The Abel–Jacobi block and dictionary at level $M/p$.* The hypotheses `hDQ₀`, `hPQ₀`, `ajQ₀`, `hajQ₀ε`, `hajQ₀`, `kQ₀`, `hkQ₀₁`, `hkQ₀₂`, `ajbar₀`, `hajbar₀`, `hajbar₀_over`, `εbar₀`, `hεbar₀`, `hεbar₀_aj` are the exact analogues at level $M/p$ of the corresponding level-$M$ hypotheses above, with `D₀`, the model `toBase p (ΓN p M H hpM) hj`, the rigidifying section `𝔛.εinf` followed by `𝔛.π`, and the curve model `Meta₀` in place of their level-$M$ counterparts. The bijection `pts₀` identifies `JH (M / p) (infSubgroup p M H hpM)` with the $\overline{\mathbb{Q}}$-points of `D₀.toBase` over `genPt p`; `hpts₀_add` states that it is additive for the relative group law attached to `hD₀`, and `hpts₀_aj` the Abel–Jacobi pin for `Meta₀`, `ajbar₀` and the cusp section `𝔛.εinf` followed by `𝔛.π`.
--
--   *The pull-backs and the classifying morphisms.* It is assumed that `xHFunctionFieldBar M H` has principal divisors over $\overline{\mathbb{Q}}$. The family `αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H)` is pinned on divisor classes by `hpull0` and `hpull1`: `αpull 0` (respectively `αpull 1`) sends the class of a degree-zero divisor $D_w$ downstairs to the class of any degree-zero divisor upstairs equal to the divisor pull-back of $D_w$ along $\alpha_H$ (respectively along $\beta_H$). The family `degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase` consists of morphisms $D_0 \to D$ over `Spec (R p)`, and `hdegPull` is their classifying property: for each $i$, each scheme $T$ with $t : T \to \operatorname{Spec}(R p)$ and each $T$-point $b$ of `D₀.toBase` over $t$, the pullback of `hD.poincare` along $b$ followed by `degPull i` has underlying module isomorphic to the rigidification, in the sense of `Scheme.Modules.rigidify` along the section `rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf` and the projection `pullback.snd (toBase p (ΓM M H) hj) t`, of the module pullback along `curveChange` of `𝔛.π` (for $i = 0$) or of `𝔛.πw` (for $i = 1$) at $t$ of the module underlying the pullback of `hD₀.poincare` along $b$.
--
--   *Conclusion.* For every $i \in \mathrm{Fin}\,2$ and every $x \in$ `JH (M / p) (infSubgroup p M H hpM)`, the underlying morphism of the $\overline{\mathbb{Q}}$-point $\mathrm{pts}(\mathrm{αpull}\;i\;x)$ of $D$ equals the underlying morphism of $\mathrm{pts}_0(x)$ followed by the underlying morphism of $\mathrm{degPull}\;i$.
--
--   This is the compatibility statement saying that the two morphisms $D_0 \to D$ classifying the pull-back of the Poincaré bundle along the degeneracy morphisms `𝔛.π` and `𝔛.πw`, re-rigidified at the cusp, induce on $\overline{\mathbb{Q}}$-points, through the two Abel–Jacobi dictionaries `pts` and `pts₀`, exactly the divisor pull-back maps $\alpha_H^*$ and $\beta_H^*$ from $J_H(M/p)$ to $J_H(M)$. It is used by [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords) to assemble the Néron-model object of $J_H(M)$ at $p$ together with its degeneracy structure, as needed for level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_pts_alphaPull_eq_pts_levelN_comp_degPull.lean

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

theorem ModularCurve.XHDRModelAtP.pts_alphaPull_eq_pts_levelN_comp_degPull
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

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
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    [IsProper (toBase p (ΓN p M H hpM) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
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

    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (hpull0 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)
    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L)))
    :
    ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (pts (αpull i x)).1 = (pts₀ x).1 ≫ (degPull i).1 := by sorry
