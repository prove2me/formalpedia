-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField
-- name    : ModularCurve.DRModelPackageLevel.abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/74546f60-f524-5c4a-8f22-23883d5acf9f
-- title:
--   Reduction killed by both restriction maps when glued Pic⁰-pair vanishes
-- statement:
--   Setting. Fix $N_0\in\mathbb N$ and a prime $p$ with $p\nmid N_0$, and let $\mathfrak P$ be a package `DRModelPackageLevel N₀ p hpN₀` for the two Igusa-type models `toBase N₀ p : X N₀ p ⟶ Spec (R p)` (level $N_0p$) and `toBase0 N₀ p : X0 N₀ p ⟶ Spec (R p)` (level $N_0$) over the base ring `R p`; among its data are the section `𝔓.εinf` of `toBase N₀ p`, the degeneracy `𝔓.π` over the base, the endomorphism `𝔓.w`, the two maps `𝔓.comp κ toκ i` ($i\in\{0,1\}$) from the base change of `toBase0 N₀ p` into the fibre `fibre toκ` of `toBase N₀ p`, the subset `𝔓.smoothLocus` of `X N₀ p`, the curve model `𝔓.Meta` over $\overline{\mathbb Q}$ with function field `modularFunctionFieldBar (N₀ * p)` together with the comparison isomorphism `𝔓.eeta` onto the geometric generic fibre, and the curve models `𝔓.Mfib κ toκ` with their comparison maps `𝔓.efib`. Fix further a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA`) and a ring homomorphism $\rho : R p \to A$ whose composite with the inclusion $A\subseteq\overline{\mathbb Q}$ is the structure map (`hρ`). Write $\kappa=\mathrm{ResidueField}\,A$; it has characteristic $p$ and is an `R p`-algebra through $\mathrm{residue}\circ\rho$, and the Hecke-algebra module structures on `JZero (N₀ * p)` and `JZero N₀` are installed.
--
--   The assertion then quantifies over the following groups of data and hypotheses.
--
--   (i) Representability over `R p`. A relative $\mathrm{Pic}^0$ designation `D` for `toBase N₀ p` (a scheme `D.P` over $\mathrm{Spec}(R p)$ with a zero section) together with `hD`, which says that `D` represents, with Poincaré bundle `hD.poincare`, the functor of line bundles on the pullback of `toBase N₀ p`, rigidified along `𝔓.εinf`, that are algebraically equivalent to zero on every geometric fibre (the cut `algEquivZeroCut`), the universal property and triviality along the zero section being part of the structure. Also: `D.toBase` is separated; a hypothesis requiring that every point $y$ of the special fibre `fibre (algebraMap (R p) κ)` which does not lie simultaneously in the images of the base maps of `𝔓.comp κ _ 0` and `𝔓.comp κ _ 1` has its image under `pullback.fst` in `𝔓.smoothLocus`; a section `ε₀` of `toBase0 N₀ p`; and a designation `D₀` with `hD₀` expressing the same representability for `toBase0 N₀ p` rigidified along `ε₀`. Properness of the base changes of both structure maps to $\kappa$, and smoothness of relative dimension $1$ and geometric integrality of the base change of `toBase0 N₀ p` to $\kappa$, are assumed.
--
--   (ii) The $\kappa$-fibre and the two restriction maps. Hypotheses `hDκ` and `hD₀κ` say that `D.baseChange κ` and `D₀.baseChange κ` represent the corresponding functors for the base-changed curves, rigidified along `sectionBaseChange κ 𝔓.εinf` and `sectionBaseChange κ ε₀`; two further hypotheses provide isomorphisms identifying `hDκ.poincare.L` and `hD₀κ.poincare.L` with the base changes (`BaseChange.ofR`) of the pullbacks of `hD.poincare` and `hD₀.poincare` along the respective first projections. The hypothesis `hε₁'` states that the section `sectionBaseChange κ ε₀` followed by `𝔓.comp κ _ 0` is `sectionBaseChange κ 𝔓.εinf`. Finally `abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase` is a pair of morphisms over $\mathrm{Spec}\,\kappa$, pinned down by two hypotheses: `abq 0` is the classifying map `RepresentsRelSubPic.pullbackHom` attached to `𝔓.comp κ _ 0` (with its compatibility `𝔓.comp_over` and `hε₁'`), and for every scheme $T$ over $\mathrm{Spec}\,\kappa$ and every $T$-point $a$ of `(D.baseChange κ).toBase` the bundle of `hD₀κ.poincare` pulled back along $a$ followed by `abq 1` is isomorphic to the rigidification (`Scheme.Modules.rigidify` along `rigSection`) of the pullback of `(hDκ.poincare.pullbackAlong a).L` along `curveChange` of `𝔓.comp κ _ 1`.
--
--   (iii) Abel–Jacobi data over $\mathbb Q$ and over $\overline{\mathbb Q}$. `hDQ` and `hPQ` are the analogues over $\mathbb Q$ of `hDκ` and its Poincaré comparison; the base change of `toBase N₀ p` to $\mathbb Q$ is separated. A morphism `ajQ` over the $\mathbb Q$-curve to `(D.baseChange ℚ).toBase` is given with `hajQε`, saying that `sectionBaseChange ℚ 𝔓.εinf` followed by `ajQ` is the zero section of `D.baseChange ℚ`, and `hajQ`, saying that for every field $K$, every $t : \mathrm{Spec}\,K \to \mathrm{Spec}\,\mathbb Q$ and every point $x$ of the $\mathbb Q$-curve over $t$, the Poincaré bundle of `hDQ` pulled back along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the point $t$ followed by `sectionBaseChange ℚ 𝔓.εinf` — that is, `ajQ` realises $x\mapsto [x]-[\infty]$. A morphism `kQ` from the geometric generic fibre `pullback (toBase N₀ p) (genPt p)` to the $\mathbb Q$-fibre is given with `hkQ₁`, `hkQ₂` expressing its compatibility with the two projections (the second up to $\mathrm{Spec}$ of $\mathbb Q\to\overline{\mathbb Q}$). A morphism `ajbar : 𝔓.Meta.C ⟶ D.P` is given with `hajbar`, identifying it with `𝔓.eeta` followed by `kQ`, `ajQ` and `pullback.fst`, and `hajbar_over`, saying it lies over `𝔓.Meta.toBase` followed by `genPt p`. A geometric point `εbar` of `𝔓.Meta.C` is given with `hεbar`, matching it with `𝔓.εinf` through `𝔓.eeta`, and `hεbar_aj`, saying that `εbar` followed by `ajbar` is `genPt p` followed by the zero section of `D`.
--
--   (iv) The dictionary. A bijection `pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase` between $\mathrm{Pic}^0$ of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb Q}$ and the geometric points of `D`, subject to: additivity with respect to the relative group law attached to `hD` by `RepresentsRelSubPic.relativeGroupLaw` for `algEquivZeroGroupCut`; Galois equivariance, $(\mathrm{pts}(\sigma\cdot x))$ being $\mathrm{Spec}(\sigma)$ followed by $\mathrm{pts}(x)$; and compatibility with `ajbar` on differences of points, namely for all geometric points $x,s$ of `𝔓.Meta.C` with $s$ matching `𝔓.εinf` through `𝔓.eeta` there is a degree-zero divisor $D_v$ whose underlying divisor is `Finsupp.single` at the place of $x$ minus `Finsupp.single` at the place of $s$ (places taken via `𝔓.Meta.pointEquivPlace`) with $(\mathrm{pts}(\mathrm{Pic0.mk}\,D_v))$ equal to $x$ followed by `ajbar`.
--
--   (v) Reduction of places. Data `data : ModularPolynomialData p` with the Kronecker congruence `hKr`; the integrality hypotheses `hα`, `hβ` for the two Hecke embeddings `heckeAlphaBar`, `heckeBetaBar` of `modularFunctionFieldBar` at level $N_0$, $p$ over $\overline{\mathbb Q}$; a place specialisation `P : PlaceSpecialization A p N₀ data hKr κ (residue A) hα hβ`, whose derived maps `P.reduceFst`, `P.reduceSnd` send a place of `modularFunctionFieldBar (N₀ * p)` to the specialisation `P.sp` of its restriction along `heckeAlphaBar`, respectively `heckeBetaBar`; a finite set $W$ of places of `modularFunctionFieldC κ N₀` characterised by the hypothesis that $w\in W$ if and only if $w$ lies in `ssPlaces p N₀ κ`. Two further hypotheses relate points and places at strict places: for every geometric point $y$ of `𝔓.Meta.C`, every $A$-point $u$ of `toBase N₀ p` whose generic point is $y$ (composition with `barPt A` equals $y$ followed by `𝔓.eeta` and `pullback.fst`), every $\kappa$-point $u_\kappa$ of the special fibre which is the reduction of $u$ (its composites with the two projections being $\mathrm{Spec}$ of the residue map followed by $u$, and the identity), and under the assumption that the place of $y$ is strict of the first or second kind in the sense of `P.IsStrictFst`/`P.IsStrictSnd`, every closed point $P_0$ (respectively $P_1$) of `(𝔓.Mfib κ _).C` whose image under `𝔓.efib` is the image of the closed point of $\kappa$ under $u_\kappa$ followed by `fibreMap0 𝔓.π` (respectively under $u_\kappa$ followed by `fibreMap 𝔓.w.hom 𝔓.w_over` and then `fibreMap0 𝔓.π`) satisfies `placeOfPoint P₀ = P.reduceFst` of the place of $y$ (respectively `placeOfPoint P₁ = P.reduceSnd` of that place).
--
--   (vi) The class, its representative and its reduction. A class $x \in$ `JZero (N₀ * p)`; a degree-zero divisor $E$ on `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb Q}$ which is good in the sense of `P.IsGoodDiv`, i.e. every place in its support is strict of the first or second kind; an admissible gluing datum $g$ for the node pairs $S=$ `nodePairsOfPlaces (arithFrobC p κ N₀) W` (a triple consisting of two divisors of degree zero, vanishing at the first, respectively second, member of each node pair, together with a family of units), subject to the hypothesis that $g$ equals `P.glueData S E`, that is, the pair of push-forwards of the first and second parts of $E$ along `P.reduceFst` and `P.reduceSnd`, with trivial unit component; the hypothesis `Pic0.mk E = x`; an $A$-point $s$ of `D.toBase` with $(\mathrm{pts}\,x)$ equal to `barPt A` followed by $s$; and a $\kappa$-point $s_\kappa$ of `(D.baseChange κ).toBase` over the identity of $\mathrm{Spec}\,\kappa$ whose composite with `pullback.fst` is $\mathrm{Spec}$ of the residue map followed by $s$.
--
--   Conclusion. Assume that the class of $g$ in `GluedPic0 κ (modularFunctionFieldC κ N₀) S` has vanishing image under `GluedPic0.toPic0Pair S`, i.e. both divisor components of $g$ are trivial in $\mathrm{Pic}^0$ of `modularFunctionFieldC κ N₀` over $\kappa$. Then for each $i : \mathrm{Fin}\,2$ the composite $\kappa$-point [`NeronModelInfra.schemeHomOverComp sκ (abq i)`](def/AlgebraicGeometry_NeronModelEndomorphismExtension.html#L25) of `(D₀.baseChange κ).toBase` equals the neutral element `one (𝟙 (Spec κ))` of the relative group law attached to `hD₀` by `RepresentsRelSubPic.relativeGroupLaw` for `algEquivZeroGroupCut` and base changed along `specMap (R p) κ`.
--
--   This is the torus-slice step in the comparison of the Deligne–Rapoport special fibre at $p$ with the two copies of $\mathrm{Pic}^0$ of the level-$N_0$ curve: for a class represented by a divisor all of whose places are strict, triviality of the associated gluing datum in $\mathrm{Pic}^0\times\mathrm{Pic}^0$ forces the reduction of the corresponding point to be annihilated by both restriction maps $\mathrm{abq}_0,\mathrm{abq}_1$, i.e. to lie in the toric part of the special fibre. No Galois- or inertia-invariance of the class is assumed. It is used by [`ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization`](thm.html#ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField.lean

import Mathlib
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
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :

    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    ∀
      (D : RelativePic0Designation (R p) (toBase N₀ p))
      (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

      (_ : IsSeparated D.toBase)

      (_ : ∀ (y : ↥(fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))),
          ¬ (y ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base ∧
              y ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base) →
            (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).base y ∈
              (𝔓.smoothLocus : Set (X N₀ p)))
      (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
      (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
      (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)
      [IsProper (baseChange (R p) (toBase N₀ p) (ResidueField ↥A))]
      [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))] [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      [GeometricallyIntegral (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)) (D.baseChange (ResidueField ↥A)))

      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A)
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) ε₀)) (D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ (ResidueField ↥A)
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hε₁' : (sectionBaseChange (ResidueField ↥A) ε₀).1 ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0 = (sectionBaseChange (ResidueField ↥A) 𝔓.εinf).1)
      (abq : Fin 2 → SchemeHomOver (D.baseChange (ResidueField ↥A)).toBase (D₀.baseChange (ResidueField ↥A)).toBase)

      (_ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        hε₁' hDκ hD₀κ)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t (sectionBaseChange (ResidueField ↥A) ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t)
            ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)
              (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) t)).obj (hDκ.poincare.pullbackAlong a).L)))

      (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
      (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
          (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

      (_ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

      (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
      (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
      (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                (Category.comp_id t)))).idealModule))

      (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
      (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
      (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

      (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
      (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)
      (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
      (_ : ∀ x y : JZero (N₀ * p),
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
      (_ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
        (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
      (_ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
          (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
            Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

      (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (W : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀))) (_ : ∀ w, w ∈ W ↔ w ∈ ssPlaces p N₀ (ResidueField ↥A))

      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) (ResidueField ↥A)) ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y))

      (x : JZero (N₀ * p))
      (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
      (_ : P.IsGoodDiv (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))))
      (g : ↥(GluingData.admissible (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)))
      (_ : (g : GluingData (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)) =
        P.glueData (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) E)
      (_ : Pic0.mk E = x)
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
      (_ : (pts x).1 = barPt A ≫ s.1)
      (sκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (D.baseChange (ResidueField ↥A)).toBase)
      (_ : sκ.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1),
      GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)
          (GluedPic0.mk (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) g) = 0 →
        ∀ i : Fin 2,
          NeronModelInfra.schemeHomOverComp sκ (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) (ResidueField ↥A))).one
              (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) := by sorry
