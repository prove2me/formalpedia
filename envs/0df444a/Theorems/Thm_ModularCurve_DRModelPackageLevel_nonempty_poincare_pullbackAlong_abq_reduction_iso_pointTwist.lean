-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_abq_reduction_iso_pointTwist
-- name    : ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_abq_reduction_iso_pointTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/66fdc0a2-c843-57cb-8766-9f7d62b4a4a1
-- title:
--   The two abq coordinates of a reduced Abel–Jacobi point
-- statement:
--   Setting. Let $N_0$ and $p$ be nonzero natural numbers with $p$ prime and $p \nmid N_0$, and let $\mathfrak P$ be a model package `DRModelPackageLevel N₀ p hpN₀` for the two modular curves over the base ring `R p`: the level-$N_0p$ curve with structure morphism `toBase N₀ p` and the level-$N_0$ curve with structure morphism `toBase0 N₀ p`. Among the data of $\mathfrak P$ used below are the cuspidal section `𝔓.εinf` of `toBase N₀ p`, the open subset `𝔓.smoothLocus` of `X N₀ p`, for each base field the two morphisms `𝔓.comp` from the base change of `toBase0 N₀ p` to the fibre of `toBase N₀ p` together with their compatibilities `𝔓.comp_over` over the base, the curve model `𝔓.Meta` over $\overline{\mathbb Q}$ of the function field `modularFunctionFieldBar (N₀ * p)` with its bijection `𝔓.Meta.pointEquivPlace` between $\overline{\mathbb Q}$-points of `𝔓.Meta.C` and places, and the isomorphism `𝔓.eeta` from `𝔓.Meta.C` to the $\overline{\mathbb Q}$-fibre of `toBase N₀ p`.
--
--   Let $A$ be a valuation subring of `AlgebraicClosure ℚ` with `hA : A.LiesOverPrime p`, that is, $p$ is a non-unit of $A$, and let $\rho :$ `R p` $\to A$ be a ring homomorphism such that $\rho$ followed by the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is the structural map `algebraMap (R p) (AlgebraicClosure ℚ)`. Write $\kappa$ for `ResidueField ↥A`; it is of characteristic $p$, and it is made an `R p`-algebra through $\rho$ followed by the residue map. The statement is elaborated with the Hecke-module structures `heckeModuleBar (N₀ * p)` and `heckeModuleBar N₀` on the degree-zero class groups in scope; they do not occur in the conclusion.
--
--   All the following data and hypotheses are universally quantified.
--
--   Representability at level $N_0p$ over `R p`. A designation $D$, that is a scheme over `Spec (R p)` with a zero section, together with `hD`: a Poincaré rigidified line bundle on `D.toBase` whose fibres are algebraically trivial of degree zero in the sense of `algEquivZeroCut`, satisfying the universal property that any such rigidified bundle on a base $T$ is pulled back from the Poincaré bundle along a unique $T$-point of `D.toBase`, and trivial along the zero section; and the hypothesis that `D.toBase` is separated.
--
--   Reduction hypothesis. Every point $y$ of the $\kappa$-fibre `fibre (algebraMap (R p) κ)` of `toBase N₀ p` which fails to lie simultaneously in the images of both component maps `𝔓.comp κ _ 0` and `𝔓.comp κ _ 1` has its image under the first projection contained in `𝔓.smoothLocus`.
--
--   Representability at level $N_0$ over `R p`. A section $\varepsilon_0$ of `toBase0 N₀ p`, a designation $D_0$ and a representability datum `hD₀` for `toBase0 N₀ p` with respect to $\varepsilon_0$, of the same shape as `hD`. Geometric hypotheses on the $\kappa$-base changes are assumed: properness of the base changes of `toBase N₀ p` and of `toBase0 N₀ p`, and smoothness of relative dimension $1$ and geometric integrality of the base change of `toBase0 N₀ p`.
--
--   Special-fibre comparison data. `hDκ`: the base change $D \times_{R p} \kappa$ represents the relative sub-Picard functor of the $\kappa$-base change of `toBase N₀ p` with section `sectionBaseChange κ 𝔓.εinf`; a hypothesis that the Poincaré bundle of `hDκ` is isomorphic to the bundle obtained by `BaseChange.ofR` from the pullback of the Poincaré bundle of `hD` along the first projection; the analogous pair `hD₀κ` and its Poincaré comparison isomorphism at level $N_0$ with section `sectionBaseChange κ ε₀`; and `hε₁'`: the base-changed section $\varepsilon_0$ followed by the component map `𝔓.comp κ _ 0` equals the base-changed section `𝔓.εinf`.
--
--   The two component morphisms. A family `abq : Fin 2 → SchemeHomOver` of morphisms from $(D\times_{R p}\kappa)$`.toBase` to $(D_0\times_{R p}\kappa)$`.toBase` over the base, pinned as follows: `abq 0` is the classifying morphism `RepresentsRelSubPic.pullbackHom` attached to the component map `𝔓.comp κ _ 0`, its compatibility `𝔓.comp_over`, `hε₁'`, `hDκ` and `hD₀κ`; and `abq 1` satisfies, for every scheme $T$ with a morphism $t$ to `Spec κ` and every $T$-point $a$ of $(D\times_{R p}\kappa)$`.toBase` over $t$, that the Poincaré bundle of `hD₀κ` pulled back along $a$ followed by `abq 1` is isomorphic to the `rigidify` (with respect to `rigSection` for `sectionBaseChange κ ε₀` and the second projection) of the pullback, along the curve change attached to `𝔓.comp κ _ 1`, of the Poincaré bundle of `hDκ` pulled back along $a$.
--
--   Generic-fibre Abel–Jacobi block. `hDQ` and `hPQ`: the base change $D\times_{R p}\mathbb Q$ represents the relative sub-Picard functor of the $\mathbb Q$-base change of `toBase N₀ p` with section `sectionBaseChange ℚ 𝔓.εinf`, and its Poincaré bundle is isomorphic to the one obtained by `BaseChange.ofR` from `hD.poincare` pulled back along the first projection; separatedness of the $\mathbb Q$-base change; a morphism `ajQ` over the base from the $\mathbb Q$-curve to $(D\times_{R p}\mathbb Q)$`.toBase` with `hajQε`: the cuspidal section followed by `ajQ` is the zero section, and `hajQ`: for every field $K$, every morphism $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of the $\mathbb Q$-curve over $t$, the Poincaré bundle of `hDQ` pulled back along $x$ followed by `ajQ` is isomorphic to the tensor product of the `lineBundle` (the dual ideal module) of the degree-one relative effective Cartier divisor of the point $x$ with the `idealModule` of the divisor of the point $t$ followed by the cuspidal section — the Abel–Jacobi normalisation $x \mapsto [x - \infty]$. Further, a morphism `kQ` from the $\overline{\mathbb Q}$-fibre to the $\mathbb Q$-fibre of `toBase N₀ p` with the two projection compatibilities `hkQ₁`, `hkQ₂`; a morphism `ajbar` from `𝔓.Meta.C` to `D.P` equal to `𝔓.eeta` followed by `kQ`, `ajQ` and the first projection, lying over `𝔓.Meta.toBase` followed by `genPt p`; a $\overline{\mathbb Q}$-point `εbar` of `𝔓.Meta.C` which maps to the cuspidal section `𝔓.εinf` in the fibre and satisfies `εbar` followed by `ajbar` $=$ `genPt p` followed by the zero section of $D$; and a bijection `pts` from `JZero (N₀ * p)`, the group of degree-zero divisor classes of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb Q}$, to the $\overline{\mathbb Q}$-points of `D.toBase` over `genPt p`, subject to three clauses: additivity of `pts` for the relative group law of `hD` attached to `algEquivZeroGroupCut`; Galois equivariance, $\mathrm{pts}(\sigma\cdot x) = \operatorname{Spec}(\sigma)$ followed by $\mathrm{pts}(x)$ for every $\sigma \in \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$; and the Abel–Jacobi clause: for all $\overline{\mathbb Q}$-points $x, s$ of `𝔓.Meta.C` such that $s$ maps to the cuspidal section, there is a degree-zero divisor $D_v$ equal to $\mathrm{single}(\text{place of }x) - \mathrm{single}(\text{place of }s)$ whose class satisfies $\mathrm{pts}([D_v]) = x$ followed by `ajbar`.
--
--   The enumerated divisor. A natural number $n$; a family `qq` of $\overline{\mathbb Q}$-points of `𝔓.Meta.C`; a family `ss` of $A$-points of `toBase N₀ p` over $\operatorname{Spec}\rho$; the compatibility that each `qq i`, transported by `𝔓.eeta` and the first projection, equals `barPt A` followed by `ss i`; multiplicities `pos`, `neg` $: \mathrm{Fin}\,n \to \mathbb N$ with $\sum_i (\mathrm{pos}_i - \mathrm{neg}_i) = 0$; a degree-zero divisor $D_x$ equal to $\sum_i \mathrm{single}(\text{place of } \mathrm{qq}_i)(\mathrm{pos}_i - \mathrm{neg}_i)$; an $A$-point $s$ of `D.toBase` with $\mathrm{pts}([D_x]) =$ `barPt A` followed by $s$; and a $\kappa$-point $s_\kappa$ of $(D\times_{R p}\kappa)$`.toBase` whose first projection is the residue map followed by $s$, i.e. the reduction of $s$.
--
--   Component labelling. A labelling $c : \mathrm{Fin}\,n \to \mathrm{Fin}\,2$; $\kappa$-points `y i` of the $\kappa$-fibre of `toBase N₀ p` whose first projection is the residue map followed by `ss i` and whose second projection is the identity; the condition that the image of each `y i` lies in the image of the component map `𝔓.comp κ _ (c i)`; $\kappa$-points `z i` of the $\kappa$-base change of `toBase0 N₀ p`, sections over $\operatorname{Spec}\kappa$ by `hz`, with `z i` followed by `𝔓.comp κ _ (c i)` equal to `y i`; the condition that the closed point of each `y i` does not lie in the image of the other component map `𝔓.comp κ _ (1 - c i)`; and the bidegree condition that for each $j \in \mathrm{Fin}\,2$, $\sum_{c_i = j} (\mathrm{pos}_i - \mathrm{neg}_i) = 0$.
--
--   Conclusion. The conjunction of two non-emptiness assertions for isomorphism types of line bundles on the $\kappa$-base change of the level-$N_0$ curve (pulled back along the identity of $\operatorname{Spec}\kappa$).
--
--   First, the Poincaré bundle of `hD₀κ` pulled back along $s_\kappa$ followed by `abq 0` is isomorphic to the right fold over `List.finRange n`, starting from the monoidal unit, of the operation that sends $(i, M)$ to $M$ when $c_i \neq 0$ and, when $c_i = 0$, to
--   $$\bigl(I_{z_i}^{\mathrm{pos}_i}\bigr)^{\mathrm{inv}} \otimes \bigl(I_{z_i}^{\mathrm{neg}_i}\bigr) \otimes M,$$
--   where $I_{z_i}$ is the ideal sheaf of the degree-one relative effective Cartier divisor `RelEffCartierDiv.ofPoint` of the section `z i`, its `invModule` being the dual of the module of the ideal sheaf and its `module` the ideal sheaf module itself.
--
--   Second, the Poincaré bundle of `hD₀κ` pulled back along $s_\kappa$ followed by `abq 1` is isomorphic to the `rigidify`, with respect to `rigSection` for the identity of $\operatorname{Spec}\kappa$ and `sectionBaseChange κ ε₀` and the second projection, of the analogous right fold in which only the indices with $c_i = 1$ contribute the factor $\bigl(I_{z_i}^{\mathrm{pos}_i}\bigr)^{\mathrm{inv}} \otimes \bigl(I_{z_i}^{\mathrm{neg}_i}\bigr)$.
--
--   The result computes the two component coordinates of the reduction at $p$ of the point of the relative $\mathrm{Pic}^0$ attached to a degree-zero divisor class $[D_x]$ on the modular curve of level $N_0p$: along the first abelian-quotient map the reduction is the untwisted product of the divisors $z_i$ supported on one component of the Deligne–Rapoport fibre, along the second it is its rigidified analogue on the other component. It is cited by the statement identifying the pair of component coordinates of a glued specialisation with the corresponding pair of $\mathrm{Pic}^0$ classes, a step in the analysis of the reduction of $J_0(N_0p)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_abq_reduction_iso_pointTwist.lean

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

theorem ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_abq_reduction_iso_pointTwist
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

      {n : ℕ} (qq : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (ss : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : ∀ i, (qq i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = Spec.map (CommRingCat.ofHom A.subtype) ≫ (ss i).1)
      (pos neg : Fin n → ℕ) (_ : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0)
      (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
      (_ : (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
        ∑ i, Finsupp.single (𝔓.Meta.pointEquivPlace (qq i)) ((pos i : ℤ) - (neg i : ℤ)))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
      (_ : (pts (Pic0.mk Dx)).1 = barPt A ≫ s.1)
      (sκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (D.baseChange (ResidueField ↥A)).toBase)
      (_ : sκ.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
      (c : Fin n → Fin 2)
      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))))
      (_ : ∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (ss i).1)
      (_ : ∀ i, y i ≫ pullback.snd _ _ = 𝟙 _)
      (_ : ∀ i, Set.range (y i).base ⊆ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i)).base)
      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (_ : ∀ i, z i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i)
      (_ : ∀ i, (y i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - c i)).base)
      (_ : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp sκ (abq 0))).L ≅
        ((List.finRange n).foldr
          (fun i M => if c i = 0 then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
            else M)
          (𝟙_ _))) ∧
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp sκ (abq 1))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) ε₀))
          (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _))
          ((List.finRange n).foldr
            (fun i M => if c i = 1 then
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
                ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
              else M)
            (𝟙_ _))) := by sorry
