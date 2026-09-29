-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_of_isGoodClass
-- name    : ModularCurve.DRModelPackageLevel.extendsToPlace_pts_of_isGoodClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/4e5f805a-1fe3-5862-8a20-3de56601b487
-- title:
--   Good classes extend to A-points of relative Pic⁰
-- statement:
--   Fix a nonzero $N_0$ and a prime $p$ with $p \nmid N_0$, and a Deligne–Rapoport model package $\mathfrak P$ of level $N_0p$ over $R\,p = \mathbf Z_{(p)}$, with proper structure morphism `toBase N₀ p`. Let $D$ be a relative $\mathrm{Pic}^0$ designation over $R\,p$ (a scheme with structure morphism and a zero section) and $hD$ a datum exhibiting $D$ as representing, with Poincaré bundle, the functor of rigidified line bundles that are fibrewise algebraically equivalent to zero, rigidified along the cusp section $\mathfrak P.\varepsilon_\infty$; let $hDQ$ be the analogous datum for the base change to $\mathbf Q$, and $hPQ$ an isomorphism of its Poincaré bundle with the $\mathbf Q$-descent of the pullback of the Poincaré bundle of $hD$ along the first projection of $D.P \times_{R p} \mathbf Q$. Further data: a morphism $ajQ$ from the generic fibre curve to $D_{\mathbf Q}$ sending the cusp section to the zero section and satisfying, for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbf Q$ and every $K$-point $x$ of the curve, an isomorphism of the Poincaré pullback along $x \circ ajQ$ with the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the cusp section at $t$ (so $ajQ$ is Abel–Jacobi $x \mapsto [x - \infty]$); a comparison morphism $kQ$ from the geometric generic fibre to the $\mathbf Q$-fibre compatible with both projections; the induced $ajbar$ on the curve model $\mathfrak P.\mathrm{Meta}$ of $\overline{\mathbf Q}(X(N_0p))$, lying over the generic point; a $\overline{\mathbf Q}$-point $\bar\varepsilon$ of that model above $\varepsilon_\infty$ whose $ajbar$-image is the zero section; and a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0$ of the modular function field at level $N_0p$ over $\overline{\mathbf Q}$ to the $\overline{\mathbf Q}$-points of $D$, which is additive for the relative group law attached to $hD$, Galois-equivariant, and compatible with $ajbar$ in the sense that for all $\overline{\mathbf Q}$-points $x, s$ of the model with $s$ above $\varepsilon_\infty$ there is a degree-zero divisor equal to the difference of the places of $x$ and $s$ whose class is carried by $\mathrm{pts}$ to $x \circ ajbar$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ a nonunit of $A$, and $\rho : R\,p \to A$ a ring homomorphism compatible with the embedding into $\overline{\mathbf Q}$; then the residue field of $A$ has characteristic $p$. The assertion is: for every modular polynomial datum at $p$ satisfying the Kronecker congruence, integrality of the two Hecke degeneracy embeddings at level $(N_0,p)$, every place specialisation $P$ of level $N_0$ over $A$ with values in the residue field of $A$, every prolongation tuple for $P$ that is a model and satisfies the fixed-place order law, two hypotheses asserting that for $\overline{\mathbf Q}$-points of the curve model whose place is strict for $P$ the labels of closed points of the two special-fibre copies computed through the fibre maps agree with $P.\mathrm{reduceFst}$, respectively $P.\mathrm{reduceSnd}$ (summarised here), every finite set $S$ of pairs of places of the level-$N_0$ function field over the residue field, and every class $x$: if $x$ is a good class for $(P,S)$ — that is, $x$ is the class of a degree-zero divisor all of whose support places are strict for $P$ and whose gluing datum relative to $S$ is admissible — then $\mathrm{pts}(x)$ extends to a place, i.e. there is a section of $D$ over $\operatorname{Spec} A$ whose composite with $\operatorname{Spec}$ of the inclusion $A \hookrightarrow \overline{\mathbf Q}$ equals $\mathrm{pts}(x)$.
--
--   This is one implication of the Raynaud-type bridge between the combinatorial condition on a divisor class of $J_0(N_0p)$ at $p$ (support at strict places, admissible gluing datum) and the existence of an integral point of the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model over the valuation ring $A$. It is used to prove the equivalence `extendsToPlace_pts_iff_isGoodClass` and the statement `extendsToPlace_pts_smul_sub` about differences of Galois translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_of_isGoodClass.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.extendsToPlace_pts_of_isGoodClass
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
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (_hmodel : R.IsModel) (_hO : R.OrderLawFixed)

      (_hcompatFst : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_hcompatSnd : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y))
      (S : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀) ×
        Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)))
      (x : JZero (N₀ * p)),
      P.IsGoodClass S x → ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts x) := by sorry
