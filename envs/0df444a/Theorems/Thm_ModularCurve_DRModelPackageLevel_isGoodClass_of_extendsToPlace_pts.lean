-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isGoodClass_of_extendsToPlace_pts
-- name    : ModularCurve.DRModelPackageLevel.isGoodClass_of_extendsToPlace_pts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/67f58b7e-477d-55c4-b870-de36b79b8965
-- title:
--   Extension over A implies good class for P
-- statement:
--   Fix $N_0\neq 0$ and a prime $p$ with $p\nmid N_0$, a model package $\mathfrak P$ for level $N_0p$ over $R_p$ with proper structure morphism `toBase N₀ p`, and a relative $\mathrm{Pic}^0$ designation $D$ over $R_p$ (a scheme with structure morphism and a zero section). Assume: $D$ represents the rigidified line bundles that are fibrewise algebraically equivalent to zero, rigidified along $\mathfrak P.\varepsilon_\infty$ (hypothesis `hD`), its base change to $\mathbb Q$ represents the corresponding functor on the generic fibre (`hDQ`), and the two Poincaré bundles agree after base change (`hPQ`); a morphism $\mathrm{aj}_\mathbb{Q}$ from the generic fibre of the curve to $D_\mathbb{Q}$ sending $\varepsilon_\infty$ to the zero section and pulling the Poincaré bundle back, at every point $x$ over a field, to the line bundle of the Cartier divisor $(x)$ tensored with the ideal module of the divisor of $\varepsilon_\infty$; a comparison morphism $k_\mathbb{Q}$ between the geometric generic and the $\mathbb Q$-fibre, compatible with both projections; the induced Abel–Jacobi morphism $\overline{\mathrm{aj}}$ on $\mathfrak P.\mathrm{Meta}.C$ together with a base point $\overline\varepsilon$ over $\varepsilon_\infty$ killed by it; and a bijection $\mathrm{pts}$ from $JZero(N_0p)$, the degree-zero divisor class group of the modular function field at level $N_0p$ over $\overline{\mathbb Q}$, onto the points of $D$ over the geometric generic point, which is additive for the relative group law coming from `hD`, Galois-equivariant, and sends the class of $(x)-(s)$ to $x\circ\overline{\mathrm{aj}}$ for $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ over $\varepsilon_\infty$, places being read off by `pointEquivPlace`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit, and $\rho : R_p\to A$ compatible with the structure maps, so that the residue field $\kappa$ of $A$ has characteristic $p$. Then, for: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\ \kappa\ N_0$ consisting exactly of the supersingular places `ssPlaces p N₀ κ`; modular polynomial data for $p$ satisfying the Kronecker congruence; integrality of the two Hecke degeneracy embeddings at level $N_0$ and $p$; a fibre model $\mathrm{fm}$ of level $N_0$ over $A$ with values in $\kappa$, carrying a cusp chart and containing both Igusa chart algebras `chartAlgFin N₀ p` and `chartAlgInf N₀ p` in its subrings $B_{\mathrm{Fin}}$, $B_{\mathrm{Inf}}$; surjectivity of the residue map $A\to\kappa$; modular polynomial data for all divisors of $N_0$, with the reduction of $\Phi$ for $N_0$ separable over $\kappa(T)$; a place specialization $P$ at $A$ whose place map equals the one of $\mathrm{fm}$; and a prolongation tuple for $P$ satisfying `IsModel`, the regularity and node-value laws at $W$ and the fixed order law — every element $x$ of the inertia invariants $JZero(N_0p)^{I_A}$ whose point $\mathrm{pts}(x)$ extends to an $A$-point of $D$ along $\mathrm{Spec}(\rho)$ is a good class for $P$ at the node pairs $\{(w,\mathrm{Frob}\,w):w\in W\}$: its class is represented by a degree-zero divisor all of whose support places are strictly first or strictly second for $P$, and whose glue data is admissible.
--
--   This is the substantial implication in Raynaud's description of the component group of the Jacobian of a semistable curve in the Deligne–Rapoport setting: a divisor class whose point on the relative $\mathrm{Pic}^0$ specialises into the smooth locus over $A$ can be moved to a divisor supported away from the supersingular node pairs. It supplies the forward direction of the equivalence [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_iff_isGoodClass`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_iff_isGoodClass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isGoodClass_of_extendsToPlace_pts.lean

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

theorem ModularCurve.DRModelPackageLevel.isGoodClass_of_extendsToPlace_pts
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
      ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts (x : JZero (N₀ * p))) →
        P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (x : JZero (N₀ * p)) := by sorry
