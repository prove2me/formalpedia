-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_iff_isGoodClass
-- name    : ModularCurve.DRModelPackageLevel.extendsToPlace_pts_iff_isGoodClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/2533b97c-076e-5483-984d-7d9be868fbc6
-- title:
--   Extension to an A-point of relative Pic⁰ versus good classes
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, and a package $\mathfrak P$ of type `DRModelPackageLevel N₀ p hpN₀` for the Igusa-type curve `X N₀ p` over $\operatorname{Spec} R_p$, whose structure morphism `toBase N₀ p` is assumed proper; $\mathfrak P$ carries in particular a curve model $\mathfrak P.\mathrm{Meta}$ over $\overline{\mathbf Q}$ with function field the modular function field of level $N_0p$, the comparison isomorphism $\mathfrak P.\mathrm{eeta}$, and the sections $\mathfrak P.\varepsilon_\infty$. The data are: a relative $\mathrm{Pic}^0$ designation $D$ over $R_p$ (a scheme with structure morphism and zero section) together with `hD`, the assertion that $D$ represents, with Poincaré bundle `hD.poincare`, the functor of $\mathfrak P.\varepsilon_\infty$-rigidified line bundles that are fibrewise algebraically trivial; the same over $\mathbf Q$ for the base-changed designation (`hDQ`) plus an isomorphism `hPQ` of its Poincaré bundle with the base change of `hD.poincare`; an Abel–Jacobi morphism `ajQ` over $\mathbf Q$ carrying the $\infty$-section to the zero section (`hajQε`) and realising, for every field $K$ over $\mathbf Q$ and every $K$-point $x$ of the curve, the class of $(x)-(\infty)$ (`hajQ`); a comparison morphism `kQ` between the geometric generic fibre and the $\mathbf Q$-fibre with its two compatibilities; the resulting map `ajbar` from $\mathfrak P.\mathrm{Meta}.C$ to $D.P$ over `genPt p`, a base point $\bar\varepsilon$ pinned to $\varepsilon_\infty$ and sent by `ajbar` to the zero section; and a bijection `pts` from $J_0 = \mathrm{Pic}^0$ of the level-$N_0p$ modular function field over $\overline{\mathbf Q}$ onto the points of $D$ over `genPt p`, which is additive for the group law coming from `hD`, Galois-equivariant, and compatible with `ajbar` in the sense that for pinned points $x,s$ the class of $(\mathrm{place}\,x)-(\mathrm{place}\,s)$ goes to $x \circ \mathrm{ajbar}$. Let further $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ a non-unit of $A$, and $\rho : R_p \to A$ compatible with the inclusion into $\overline{\mathbf Q}$, so that the residue field $\kappa$ of $A$ has characteristic $p$. Then for every finite set $W$ of places of the level-$N_0$ modular function field over $\kappa$ whose members are exactly the supersingular places `ssPlaces p N₀ κ`, every modular polynomial datum for $p$ satisfying the Kronecker congruence, integrality of the two level-raising maps, every fibre model `fm` over $A$ with its cusp chart containing the images of both Igusa chart algebras, surjectivity of $A \to \kappa$, modular polynomial data for all divisors of $N_0$ with the separability hypothesis `hsepΦ`, every place specialisation $P$ whose place map equals that of `fm`, and every prolongation tuple for $P$ that is a model and satisfies the regularity law and node-value law at $W$ and the fixed-place order law, one has for all $x$ in the inertia invariants of $J_0$ at $A$: `pts x` extends to a point of $D$ over $\operatorname{Spec} A$ (i.e. factors as the canonical $\overline{\mathbf Q}$-point of $A$ followed by an $A$-point of $D$) if and only if $x$ is a good class for $P$ relative to the node pairs $\{(w, \mathrm{Frob}\cdot w) : w \in W\}$, that is, $x$ is the class of a degree-zero divisor each of whose support places is strict for the first or the second reduction and whose associated glue datum is admissible.
--
--   This is the Raynaud-style bridge identifying, on the Deligne–Rapoport model of $X_0(N_0p)$ at a prime $p \nmid N_0$, the points of $J_0(N_0p)(\overline{\mathbf Q})$ that extend to $A$-points of the relative $\mathrm{Pic}^0$ with the classes admitting a divisor representative in good position with respect to the supersingular node pairs of the special fibre. It combines the two implications proved separately together with the compatibility of the place specialisation with the two reductions, and is used in assembling the Néron object at $p$ for $J_0(N_0p)$ with its relative Picard bridge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_iff_isGoodClass.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.extendsToPlace_pts_iff_isGoodClass
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

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
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (W : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)))
      (_hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p N₀ (ResidueField ↥A))
      (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (fm : CharPModel.FibreModel N₀ A p (ResidueField ↥A) (IsLocalRing.residue ↥A))
      (cc : fm.CuspChart)
      (hfin : ∀ b : IgusaScheme.chartAlgFin N₀ p,
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
            laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
      (hinf : ∀ b : IgusaScheme.chartAlgInf N₀ p,
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
            laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BInf)
      (hred : Function.Surjective (IsLocalRing.residue ↥A))
      (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N₀ → ModularPolynomialData d)
      (hsepΦ : (((dataAll N₀ (dvd_refl N₀)).Φ.map
          (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
        (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (hP : P.sp = fm.spPlace hred dataAll hsepΦ)
      (R : PlaceSpecialization.ProlongationTuple P) (_hmodel : R.IsModel) (_hRL : R.RegularityLaw W)
      (_hNV : R.NodeValueLaw W) (_hO : R.OrderLawFixed)
      (x : ↥(inertiaInvariants A (N₀ * p))),
      ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts (x : JZero (N₀ * p))) ↔
        P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (x : JZero (N₀ * p)) := by sorry
