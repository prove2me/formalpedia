-- Prove2me | Theorems.Thm_ModularCurve_jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData
-- name    : ModularCurve.jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/b6eb9094-0821-51c7-ac55-e307fb7b5660
-- title:
--   Pull-back along φ⁻¹ intertwines the two Abel–Jacobi dictionaries
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime, together with the divisibility hypotheses $hpN_0 : p \nmid N_0$, $hpM : p \mid N_0 p$ and $hpM2 : p^2 \nmid N_0 p$. Fix a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `hA : A.LiesOverPrime p`, that is, the image of $p$ lies in the non-units of $A$, and assume the residue field of $A$ is algebraically closed; the residue field then has characteristic $p$ by [`ValuationSubring.charP_residueField_of_liesOverPrime_def`](def/WeierstrassCurve_ReductionMap.html#L57). The statement installs, as local instances, the Hecke-module structures `heckeModuleBar (N₀ * p)` and `heckeModuleBar N₀` on the relevant degree-zero Picard groups and the algebra structures on the modular function field over the residue field, so that the subsequent expressions typecheck.
--
--   **Data on the $X_\top(N_0p)$ side.** A hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in `qExpFunctionFieldC ℚ ⊤`; a Deligne–Rapoport-type integral model package `𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj` for the curve `XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj` over `Spec (R p)`, carrying among other fields a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar (N₀ * p) ⊤`, the isomorphism `𝔛.eeta` of `𝔛.Meta.C` with the base change of the model to $\overline{\mathbb{Q}}$, and the section `𝔛.εinf` of the structure morphism; a level datum `Λ : JHNeronObjectAtP.LevelData p (N₀ * p) ⊤ hpM A` and a Néron object `O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ`, consisting of a scheme `O.G` with structure morphism `O.g` to the base, a relative group law `O.L`, a bijection `O.pts : JH (N₀ * p) ⊤ ≃ SchemeHomOver (genPt p) O.g`, and the further smoothness, separatedness, properness, Hecke and specialisation data of that structure.
--
--   Further, a datum `hD` asserting that the relative $\mathrm{Pic}^0$ designation $(O.G,\ O.g,\$ unit section of `O.L`$)$ represents, in the sense of `RepresentsRelSubPic`, the sub-functor of rigidified line bundles on `XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj` rigidified along `𝔛.εinf` that are fibrewise algebraically trivial (the condition `algEquivZeroCut`): it provides a Poincaré bundle satisfying this condition, the universal property that every such rigidified bundle on a base $T$ is induced by a unique $T$-point of `O.G` over the base, and triviality of the pull-back along the zero section. A datum `hDQT` asserts the same representability after base change of everything to $\mathbb{Q}$, for the base-changed designation and the base-changed $\infty$-section. An unnamed hypothesis asserts that the base change of the model to $\mathbb{Q}$ is separated.
--
--   There are, in addition: an Abel–Jacobi morphism `ajQT` from the $\mathbb{Q}$-fibre of the model to the base-changed designation, over the base; a morphism `kQT` from the pull-back of the model along `genPt p` to its pull-back along `specMap (R p) ℚ`; a morphism `ajbarT : 𝔛.Meta.C ⟶ O.G`; and a $\overline{\mathbb{Q}}$-point `εbarT` of `𝔛.Meta.C` over its base.
--
--   The hypothesis `HAJ` is a conjunction of eleven clauses pinning these down: (1) the Poincaré bundle of `hDQT` is isomorphic to the base change to $\mathbb{Q}$ (via `BaseChange.ofR`) of the pull-back of the Poincaré bundle of `hD` along the first projection of `pullback O.g (specMap (R p) ℚ)`; (2) `ajQT` carries the base-changed $\infty$-section to the zero section of the base-changed designation; (3) for every field $K$, every morphism $t : \mathrm{Spec}\,K \to \mathrm{Spec}\,\mathbb{Q}$ and every $K$-point $x$ of the $\mathbb{Q}$-fibre over $t$, the pull-back of the Poincaré bundle of `hDQT` along $x$ followed by `ajQT` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the relative effective Cartier divisor of $t$ followed by the base-changed $\infty$-section — the characterisation of `ajQT` as $x \mapsto [x-\infty]$; (4), (5) `kQT` is compatible with both projections, commuting with the first projection and intertwining the second with `specMap ℚ (AlgebraicClosure ℚ)`; (6) `ajbarT` equals `𝔛.eeta` followed by `kQT`, by `ajQT` and by the first projection of `pullback O.g (specMap (R p) ℚ)`; (7) `ajbarT` followed by `O.g` equals `𝔛.Meta.toBase` followed by `genPt p`; (8) `εbarT` lies over the $\infty$-section, namely `εbarT.1` followed by `𝔛.eeta` and the first projection equals `genPt p` followed by `𝔛.εinf.1`; (9) `εbarT.1` followed by `ajbarT` equals `genPt p` followed by the unit section of `O.L`; (10) `O.pts` is additive for the group law `RepresentsRelSubPic.relativeGroupLaw` attached to `hD` through `algEquivZeroGroupCut`; (11) for all $\overline{\mathbb{Q}}$-points $x$, $s$ of `𝔛.Meta.C` over the base with $s$ lying over the $\infty$-section as in (8), there is a degree-zero divisor $D_v$ on `xHFunctionFieldBar (N₀ * p) ⊤` equal to `Finsupp.single` of the place of $x$ minus `Finsupp.single` of the place of $s$ (places taken through `𝔛.Meta.pointEquivPlace`) such that the $\overline{\mathbb{Q}}$-point `O.pts (Pic0.mk Dv)` is $x$ followed by `ajbarT`.
--
--   **Data on the $J_0$ side.** A level datum `Λ₀ : JZeroNeronObjectAtP.LevelData N₀ p A`, a model package `𝔓 : DRModelPackageLevel N₀ p hpN₀` for `DRLevel.X N₀ p` over `Spec (R p)` (with curve model `𝔓.Meta` over $\overline{\mathbb{Q}}$ with function field `modularFunctionFieldBar (N₀ * p)`, comparison isomorphism `𝔓.eeta` and $\infty$-section `𝔓.εinf`), and a Néron object `O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀` with scheme `O₀.G`, structure morphism `O₀.g`, group law `O₀.L` and bijection `O₀.pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) O₀.g`.
--
--   On this side the same eleven clauses appear as separately named hypotheses, with `toBase N₀ p` in place of the $X_\top$-side structure morphism, `𝔓.εinf` in place of `𝔛.εinf` and the designation built from `O₀.G`, `O₀.g` and the unit of `O₀.L`: representability `hD₀` and its base change `hDQ₀`; the Poincaré comparison `hPQ₀` (clause (1)); separatedness `hsep₀` of the base change to $\mathbb{Q}$; the Abel–Jacobi morphism `ajQ₀` with `hajQε₀` (clause (2)) and `hajQ₀` (clause (3)); the comparison morphism `kQ₀` with `hkQ₁₀`, `hkQ₂₀` (clauses (4), (5)); the morphism `ajbar₀ : 𝔓.Meta.C ⟶ O₀.G` with `hajbar₀`, `hajbar_over₀` (clauses (6), (7)); the $\overline{\mathbb{Q}}$-point `εbar₀` with `hεbar₀`, `hεbar_aj₀` (clauses (8), (9), the latter written with the zero section of the designation); the additivity `hpts_law₀` of `O₀.pts` for the group law attached to `hD₀` (clause (10)); and the Abel–Jacobi dictionary `hAJ₀` for divisors on `modularFunctionFieldBar (N₀ * p)` (clause (11)).
--
--   **Comparison data.** An equality of function fields `hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p)`; an isomorphism of models $\varphi$ from `XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj` to `DRLevel.X N₀ p`, with `hφb` and `hφb'` saying that both $\varphi.\mathrm{hom}$ and $\varphi.\mathrm{inv}$ are morphisms over `Spec (R p)` for the two structure morphisms, and `hφε`, `hφε'` saying that $\varphi$ matches the two $\infty$-sections in both directions; an unnamed hypothesis that $\varphi$ transports places compatibly, namely that whenever a $\overline{\mathbb{Q}}$-point $y$ of `𝔛.Meta.C` and a $\overline{\mathbb{Q}}$-point $y_0$ of `𝔓.Meta.C` correspond under $\varphi.\mathrm{hom}$ (after composing with the respective `eeta` and first projections), the place of $y_0$ is the image of the place of $y$ under `Place.congrRingEquiv` for the ring isomorphism `IntermediateField.equivOfEq hF`; and an additive isomorphism `e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p)` together with an unnamed hypothesis that `e` agrees pointwise with `Pic0.congr` along that same ring isomorphism.
--
--   **Conclusion** (a single assertion). For every $y$ in `JH (N₀ * p) ⊤`, the underlying morphism of the $\overline{\mathbb{Q}}$-point `O₀.pts (e y)` of `O₀.G` equals the underlying morphism of `O.pts y` followed by the underlying morphism of `RepresentsRelSubPic.pullbackHom φ.inv hφb' hφε' hD hD₀`, the Picard pull-back morphism `O.G ⟶ O₀.G` over `Spec (R p)` classifying the pull-back along $\varphi.\mathrm{inv}$ of the Poincaré bundle of `hD`.
--
--   This is the compatibility step identifying the two descriptions of the Jacobian of $X_0(N_0p)$ at $p$: the one obtained from a Deligne–Rapoport model at level $\Gamma_\top(N_0p)$ and the one obtained from the level-$N_0$ model package, asserting that the Picard pull-back along the model isomorphism intertwines the two Abel–Jacobi dictionaries of $\overline{\mathbb{Q}}$-points. It is used by [`ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge`](thm.html#ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge), which transports the finite and toric parts of the special fibre across the same comparison; the proof rests on [`AlgebraicGeometry.RelPicard.pullbackHom_points_eq_pic0_congr_of_iso`](thm.html#AlgebraicGeometry.RelPicard.pullbackHom_points_eq_pic0_congr_of_iso) together with the base-change compatibility `RepresentsRelSubPic.pullbackHom_baseChange_fst`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) [NeZero (N₀ * p)]
    (hpM : p ∣ N₀ * p) (hpM2 : ¬ p ^ 2 ∣ N₀ * p) [NeZero (N₀ * p / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [IsAlgClosed (ResidueField ↥A)] :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra

    ∀ (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj)
    (Λ : JHNeronObjectAtP.LevelData p (N₀ * p) ⊤ hpM A) (O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ)
    (hD : RepresentsRelSubPic (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf (algEquivZeroCut (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)))
      (hDQT : RepresentsRelSubPic (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ))
      (_ : IsSeparated (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ))
      (ajQT : SchemeHomOver (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ).toBase)
      (kQT : pullback (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ⟶ pullback (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ))
      (ajbarT : 𝔛.Meta.C ⟶ O.G)
      (εbarT : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (HAJ :

      Nonempty (hDQT.poincare.L ≅ (BaseChange.ofR (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQT.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ).zeroSection ∧

      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ)),
        Nonempty ((hDQT.poincare.pullbackAlong
            ⟨x.1 ≫ ajQT.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQT.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQT ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ) = pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ∧
      kQT ≫ pullback.snd (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ) = pullback.snd (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbarT = 𝔛.eeta ≫ kQT ≫ ajQT.1 ≫ pullback.fst O.g (specMap (R p) ℚ) ∧
      ajbarT ≫ O.g = 𝔛.Meta.toBase ≫ genPt p ∧
      εbarT.1 ≫ 𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ∧
      εbarT.1 ≫ ajbarT = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1 ∧

      (∀ x y : JH (N₀ * p) ⊤,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (N₀ * p) ⊤)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (N₀ * p) ⊤)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbarT)),
    ∀ (Λ₀ : JZeroNeronObjectAtP.LevelData N₀ p A) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
      (O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀)
      (hD₀ : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) (⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)))
        (hDQ₀ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
            (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) ((⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).baseChange ℚ))
        (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
            (hD₀.poincare.pullbackAlong ⟨pullback.fst O₀.g (specMap (R p) ℚ), pullback.condition⟩)).L))
        (hsep₀ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

        (ajQ₀ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) ((⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).baseChange ℚ).toBase)
        (hajQε₀ : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ₀.1 = ((⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).baseChange ℚ).zeroSection)
        (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
            (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
          Nonempty ((hDQ₀.poincare.pullbackAlong
              ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
                ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                  (Category.comp_id t)))).idealModule))

        (kQ₀ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
        (hkQ₁₀ : kQ₀ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
        (hkQ₂₀ : kQ₀ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

        (ajbar₀ : 𝔓.Meta.C ⟶ O₀.G) (hajbar₀ : ajbar₀ = 𝔓.eeta ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst O₀.g (specMap (R p) ℚ))
        (hajbar_over₀ : ajbar₀ ≫ O₀.g = 𝔓.Meta.toBase ≫ genPt p)
        (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
        (hεbar₀ : εbar₀.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj₀ : εbar₀.1 ≫ ajbar₀ = genPt p ≫ (⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).zeroSection)
      (hpts_law₀ : ∀ x y : JZero (N₀ * p),
          O₀.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (O₀.pts x) (O₀.pts y))
      (hAJ₀ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
          s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
              Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
            (O₀.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀),
    ∀ (hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p))
      (φ : XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj ≅ DRLevel.X N₀ p)
      (hφb : φ.hom ≫ DRLevel.toBase N₀ p = XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
      (hφb' : φ.inv ≫ XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj = DRLevel.toBase N₀ p)
      (hφε : 𝔛.εinf.1 ≫ φ.hom = 𝔓.εinf.1) (hφε' : 𝔓.εinf.1 ≫ φ.inv = 𝔛.εinf.1)
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
          (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ φ.hom = y₀.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) →
        𝔓.Meta.pointEquivPlace y₀ =
          Place.congrRingEquiv (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a)
            (𝔛.Meta.pointEquivPlace y)),
    ∀ (e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p))
      (_ : ∀ x : JH (N₀ * p) ⊤,
        e x = Pic0.congr (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a) x),
    ∀ y : JH (N₀ * p) ⊤,
      (O₀.pts (e y)).1 = (O.pts y).1 ≫ (RepresentsRelSubPic.pullbackHom φ.inv hφb' hφε' hD hD₀).1 := by sorry
