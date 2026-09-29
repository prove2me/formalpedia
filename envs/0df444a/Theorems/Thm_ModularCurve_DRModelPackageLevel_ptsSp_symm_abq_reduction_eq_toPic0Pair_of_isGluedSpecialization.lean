-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization
-- name    : ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7f0ed4b9-9ea1-5268-bc5f-ee7b73f59e2d
-- title:
--   Abelian coordinates of the reduction equal the glued specialisation pair
-- statement:
--   Fix an integer $N_0 \ge 1$, a prime $p$ with $p \nmid N_0$, and a Deligne–Rapoport model package $\mathfrak{P}$ of level $N_0p$ at $p$ (a `DRModelPackageLevel N₀ p hpN₀`: the Igusa-type scheme $X(N_0,p)$ over $\operatorname{Spec} R_p$ with its properness, flatness, integrality, finite-presentation and normality data, its curve model `Meta` of the function field $\overline{\mathbb Q}\,$-curve of level $N_0p$ together with the isomorphism `eeta` onto the generic geometric fibre and the Galois compatibility `hgal`, the two cusp sections $\varepsilon_\infty, \varepsilon_0$, and the further components recorded in that structure). Fix a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA : A.LiesOverPrime p`), so that the residue field $\kappa = \operatorname{ResidueField} A$ has characteristic $p$, and fix a level-$N_0$ model $M$ (`JZeroNeronObjectAtP.LevelModel N₀ p A`: a ring map $\rho : R_p \to A$ lifting $R_p \to \overline{\mathbb Q}$, the designation $D_0$ representing the relative $\operatorname{Pic}^0$ of $X_0(N_0)$ over $R_p$ rigidified along $\varepsilon_0$ with representing datum `rep`, the Abel–Jacobi map `aj₀` pinned by `haj₀ε` and `haj₀`, and the point dictionaries `pts`, `ptsSp`) whose associated level data is a Jacobian in the sense of `IsJacobian` (additivity, commutativity, Galois equivariance, Hecke equivariance and the mod-$\ell$ reduction compatibility of the dictionaries). The algebra structure $R_p \to \kappa$ used throughout is the composite of $\rho$ with the residue map, and $\operatorname{JZero}$ groups at levels $N_0$ and $N_0 p$ carry their Hecke-algebra module structures.
--
--   The statement then quantifies over the following data and hypotheses.
--
--   Representability over $R_p$: a designation $D$ of the relative $\operatorname{Pic}^0$ of $X(N_0,p)$ over $R_p$ (a scheme $D.P \to \operatorname{Spec} R_p$ with a zero section), a representing datum `hD` for the subfunctor of line bundles rigidified along $\varepsilon_\infty$ and fibrewise algebraically equivalent to zero, separatedness of $D.\mathrm{toBase}$, and the hypothesis that every point of the geometric fibre $X(N_0,p) \times_{R_p} \kappa$ not lying simultaneously in the images of the two component maps $\mathfrak{P}.\mathrm{comp}\,\kappa\,0$ and $\mathfrak{P}.\mathrm{comp}\,\kappa\,1$ maps into the smooth locus of $\mathfrak{P}$.
--
--   Geometry of the special fibre: properness of the base changes to $\kappa$ of $X(N_0,p)$ and of $X_0(N_0)$, smoothness of relative dimension $1$ and geometric integrality of the latter, representing data `hDκ` and `hD₀κ` for the base changes $D_\kappa$ and $(D_0)_\kappa$ with their sections obtained by base change, and two hypotheses asserting that the respective Poincaré bundles are isomorphic to the bundles obtained by base change from those of `hD` and of `M.rep`.
--
--   The two abelian-quotient maps: a compatibility `hε₁'` stating that the section $\varepsilon_0$ over $\kappa$ followed by the zeroth component map equals the section $\varepsilon_\infty$ over $\kappa$; a pair $\mathrm{abq} : \mathrm{Fin}\,2 \to$ morphisms $D_\kappa \to (D_0)_\kappa$ over $\kappa$, with $\mathrm{abq}\,0$ pinned as the classifying map of pullback along the zeroth component map, and $\mathrm{abq}\,1$ pinned by the requirement that for every scheme $T$ over $\kappa$ and every $T$-point $a$ of $D_\kappa$, the Poincaré bundle pulled back along $a$ followed by $\mathrm{abq}\,1$ is isomorphic to the rigidification along the section associated with $\varepsilon_0$ of the pullback, along the first component map, of the Poincaré bundle pulled back along $a$.
--
--   Generic-fibre Abel–Jacobi data: a representing datum `hDQ` for the base change of $D$ to $\mathbb Q$ and an isomorphism `hPQ` of its Poincaré bundle with the one obtained by base change from `hD`; separatedness of $X(N_0,p)_{\mathbb Q}$ over $\mathbb Q$; a morphism $\mathrm{ajQ} : X(N_0,p)_{\mathbb Q} \to (D_{\mathbb Q}).P$ over $\mathbb Q$ with `hajQε` saying that the cusp section followed by $\mathrm{ajQ}$ is the zero section, and `hajQ` saying that for every field $K$, every $\operatorname{Spec} K \to \operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of $X(N_0,p)_{\mathbb Q}$, the Poincaré bundle pulled back along $x$ followed by $\mathrm{ajQ}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the cusp; a morphism $\mathrm{kQ}$ from the geometric generic fibre to the fibre over $\mathbb Q$, compatible with the two projections via `hkQ₁` and `hkQ₂` (the second up to the inclusion $\mathbb Q \to \overline{\mathbb Q}$).
--
--   The geometric Abel–Jacobi map and the point dictionary: a morphism $\mathrm{ajbar}$ from the curve $\mathfrak{P}.\mathrm{Meta}.C$ to $D.P$ defined by `hajbar` as `eeta` followed by $\mathrm{kQ}$, $\mathrm{ajQ}$ and the first projection, lying over $\mathfrak{P}.\mathrm{Meta}.\mathrm{toBase}$ followed by the geometric generic point (`hajbar_over`); a section $\bar\varepsilon$ of $\mathfrak{P}.\mathrm{Meta}.C$ over $\overline{\mathbb Q}$ with `hεbar` identifying its image under `eeta` followed by the first projection with the cusp $\varepsilon_\infty$, and `hεbar_aj` saying that $\bar\varepsilon$ followed by $\mathrm{ajbar}$ is the zero section; a bijection $\mathrm{pts}$ from $\operatorname{JZero}(N_0p) = \operatorname{Pic}^0$ of the level-$N_0p$ function field over $\overline{\mathbb Q}$ onto the $\overline{\mathbb Q}$-points of $D$, which is additive for the relative group law determined by `hD`, is Galois equivariant, and satisfies the Abel–Jacobi normalisation: for all points $x, s$ of $\mathfrak{P}.\mathrm{Meta}.C$ over $\overline{\mathbb Q}$ with $s$ sitting over the cusp, there is a degree-zero divisor $Dv$ equal to $\delta_{w(x)} - \delta_{w(s)}$ (where $w(\cdot)$ is the place attached to a point by `Meta.pointEquivPlace`) whose class satisfies $\mathrm{pts}(\mathrm{Pic}^0.\mathrm{mk}\,Dv) = x$ followed by $\mathrm{ajbar}$.
--
--   Kronecker and specialisation data: modular polynomial data `data` for $p$ satisfying the Kronecker congruence $\Phi \bmod p = (X_1^p - X_2)(X_1 - X_2^p)$, integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke correspondence embeddings at level $(N_0,p)$, a place specialisation $P$ (a `PlaceSpecialization` for $A$, $p$, $N_0$, `data`, `hKr`, $\kappa$ and the residue map, with its map `sp` on places and its homomorphism `spPic0`), a finite set $W$ of places of the level-$N_0$ function field over $\kappa$ whose members are exactly the supersingular places `ssPlaces p N₀ κ`, and two pinning hypotheses: for every $\overline{\mathbb Q}$-point $y$ of $\mathfrak{P}.\mathrm{Meta}.C$, every $A$-point $u$ of $X(N_0,p)$ reducing onto $y$, every lift $u_\kappa$ of $u$ to the $\kappa$-fibre, and assuming $P.\mathrm{IsStrictFst}$ or $P.\mathrm{IsStrictSnd}$ holds at the place of $y$, every closed point $P_0$ (respectively $P_1$) of the curve $\mathfrak{P}.\mathrm{Mfib}\,\kappa$ whose image under $\mathfrak{P}.\mathrm{efib}\,\kappa$ is the reduction of $u_\kappa$ under the first degeneracy map (respectively under the Atkin–Lehner involution $\mathfrak{P}.w$ followed by that map) has $\mathfrak{P}.\mathrm{Mfib}\,\kappa$-place equal to $P.\mathrm{reduceFst}$ (respectively $P.\mathrm{reduceSnd}$) of the place of $y$. Here $P.\mathrm{reduceFst}$ and $P.\mathrm{reduceSnd}$ are $P.\mathrm{sp}$ applied to the restrictions of a place along the two Hecke embeddings.
--
--   Identification of function fields and of reduction maps: an equality `hE` of the intermediate fields $\mathrm{modularFunctionFieldC}\,\kappa\,N_0$ and $\mathrm{modularFunctionFieldFullC}\,\kappa\,N_0$, and the hypothesis that for every `ReductionInputsModL` datum $h$ for $A$ and $N_0$ the place reduction $\mathrm{placeReductionModL}\,h$ equals $P.\mathrm{sp}$ transported along the ring isomorphism induced by `hE`.
--
--   The torus: a natural number $t$, a morphism $\tau$ from the $t$-dimensional split torus over $\kappa$ to $D_\kappa$, and the hypothesis that for every scheme $T$ over $\kappa$ and every $T$-point $a$ of $D_\kappa$, the condition that $a$ followed by $\mathrm{abq}\,i$ is the identity element of the base-changed relative group law of `M.rep` for both $i$ is equivalent to $a$ factoring through $\tau$.
--
--   The glued specialisation: a homomorphism $\mathrm{sp}$ from the inertia invariants $\operatorname{JZero}(N_0p)^{I_A}$ to the glued $\operatorname{Pic}^0$ group attached to $\kappa$, the level-$N_0$ function field and the finite set of node pairs $\mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,p\,\kappa\,N_0, W)$ obtained by pairing each supersingular place with its arithmetic Frobenius translate; the hypothesis that $P.\mathrm{IsGluedSpecialization}$ holds for this set and $\mathrm{sp}$, i.e. that $\mathrm{sp}$ sends the class of every good degree-zero divisor to the glued class of its glue data.
--
--   Finally the point under consideration: an element $x$ of the inertia invariants whose underlying class is a good class for the node-pair set, an $A$-point $s$ of $D$ with $\mathrm{pts}(x) = \bar{A}\text{-point} \circ s$, a $\kappa$-point $s_\kappa$ of $D_\kappa$ reducing $s$, and a pair $r : \mathrm{Fin}\,2 \to$ points of $D_0$ over $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to \operatorname{Spec} R_p$ with $r\,i$ the composite of $s_\kappa$ with $\mathrm{abq}\,i$ followed by the first projection.
--
--   Under all these hypotheses the conclusion is the conjunction of two assertions.
--
--   First, the pair obtained by applying the inverse of `M.toLevelData.ptsSp` to $r\,0$ and to $r\,1$ and transporting both back along the isomorphism of $\operatorname{Pic}^0$ groups induced by `hE` equals $\mathrm{GluedPic0.toPic0Pair}$ of $\mathrm{sp}(x)$ for the node-pair set, that is, the pair of classes of the two divisor components of a representative of the glued class.
--
--   Second, $s_\kappa$ factors through $\tau$ (there exists a $\kappa$-point $y$ of the torus with $y$ followed by $\tau$ equal to $s_\kappa$) if and only if $\mathrm{GluedPic0.toPic0Pair}$ of $\mathrm{sp}(x)$ is zero.
--
--   This is the step identifying, for an inertia-invariant good class in $J_0(N_0p)(\overline{\mathbb Q})$, the two abelian coordinates of the reduction of the corresponding $A$-point of $\operatorname{Pic}^0$ of the Deligne–Rapoport model with the pair of $\operatorname{Pic}^0$-classes extracted from the glued specialisation, together with the criterion for the reduction to lie in the toric part. It is the combination of the two cited results and is used in the assembly of the level-$N_0p$ Néron object at $p$, namely by [`ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization.lean

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
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
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

theorem ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (_ : M.toLevelData.IsJacobian) :

    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
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
      [IsProper (baseChange (R p) (toBase N₀ p) (ResidueField ↥A))]
      [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))] [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      [GeometricallyIntegral (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)) (D.baseChange (ResidueField ↥A)))

      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A)
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hε₁' : (sectionBaseChange (ResidueField ↥A) M.ε₀).1 ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0 = (sectionBaseChange (ResidueField ↥A) 𝔓.εinf).1)
      (abq : Fin 2 → SchemeHomOver (D.baseChange (ResidueField ↥A)).toBase (M.D₀.baseChange (ResidueField ↥A)).toBase)

      (_ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        hε₁' hDκ hD₀κ)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t (sectionBaseChange (ResidueField ↥A) M.ε₀))
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
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) (ResidueField ↥A)) ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y))
      (hE : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀)

      (_ : ∀ h : ReductionInputsModL A N₀,
        placeReductionModL h = fun W =>
          AlgebraicCurve.Place.congrRingEquiv
            (e := (IntermediateField.equivOfEq hE).toRingEquiv)
            (he := fun a => (IntermediateField.equivOfEq hE).commutes a) (P.sp W))

      (t : ℕ) (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (D.baseChange (ResidueField ↥A)).toBase)
      (_ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t' (D.baseChange (ResidueField ↥A)).toBase),
        (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) M.rep).baseChange (specMap (R p) (ResidueField ↥A))).one t') ↔
          ∃ y : SchemeHomOver t' (torusStr (ResidueField ↥A) t),
            NeronModelInfra.schemeHomOverComp y τ = a)

      (sp : ↥(inertiaInvariants A (N₀ * p)) →+
        GluedPic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))
      (_ : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) sp)

      (x : ↥(inertiaInvariants A (N₀ * p))) (_ : P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (x : JZero (N₀ * p)))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) D.toBase)
      (_ : (pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1)
      (sκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (D.baseChange (ResidueField ↥A)).toBase)
      (_ : sκ.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)

      (r : Fin 2 → SchemeHomOver (JZeroNeronObjectAtP.resPt A ≫ Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase)
      (_ : ∀ i, (r i).1 = (NeronModelInfra.schemeHomOverComp sκ (abq i)).1 ≫ pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A))),

      ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
          (M.toLevelData.ptsSp.symm (r 0)),
        (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
          (M.toLevelData.ptsSp.symm (r 1))) =
        GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (sp x) ∧

      ((∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (torusStr (ResidueField ↥A) t), NeronModelInfra.schemeHomOverComp y τ = sκ) ↔
        GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (sp x) = 0) := by sorry
