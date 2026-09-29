-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization
-- name    : ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/8d32cf27-0890-5719-8c7f-8bc649e79893
-- title:
--   Abelian-quotient reduction of a good class matches the glued specialisation
-- statement:
--   Throughout, $N_0$ and $p$ are natural numbers with $p$ prime and $p \nmid N_0$ (hypothesis `hpN₀`), $\mathfrak{P}$ is a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀` for the level-$N_0p$ Igusa curve `X N₀ p` over the base ring `R p`, with structure morphism `toBase N₀ p : X N₀ p ⟶ Spec (R p)` and, at level $N_0$, `toBase0 N₀ p : X0 N₀ p ⟶ Spec (R p)`. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, that is $p$ lies in the nonunits of $A$, and $M$ is a `JZeroNeronObjectAtP.LevelModel N₀ p A`, i.e. a level-$N_0$ Jacobian model at $A$, comprising a ring map $\rho \colon R_p \to A$ compatible with $\overline{\mathbb{Q}}$, a section `ε₀` at infinity, a relative $\mathrm{Pic}^0$ designation `M.D₀` together with a representing datum `M.rep`, an Abel–Jacobi morphism `aj₀`, and the two dictionaries `M.pts` and `M.ptsSp`. An anonymous hypothesis asserts `M.toLevelData.IsJacobian`: the conjunction of the abelian-scheme property bundle for `M.D₀.toBase`, commutativity of the associated group law, additivity and Galois-equivariance of `pts`, additivity of `ptsSp`, agreement of the reduction of points modulo $\ell$ whenever `ReductionInputsModL A N₀` holds, and Hecke-equivariance of `pts`.
--
--   The statement is made after installing: the characteristic-$p$ structure on $\kappa :=$ `ResidueField ↥A`, the $R_p$-algebra structure on $\kappa$ given by `(IsLocalRing.residue ↥A).comp M.ρ`, and the Hecke-module structures on `JZero (N₀ * p)` and `JZero N₀`.
--
--   **Integral Picard data.** $D$ is a `RelativePic0Designation (R p) (toBase N₀ p)`, i.e. a scheme $D.P$ over $\mathrm{Spec}\,R_p$ with a zero section, and `hD` asserts that $D$ represents the rigidified relative Picard functor of `toBase N₀ p` rigidified along $\mathfrak{P}.\varepsilon_{\inf}$ and cut out by the condition `algEquivZeroCut`, i.e. fibrewise algebraic equivalence to zero: `hD` supplies a Poincaré rigidified line bundle on `pullback (toBase N₀ p) D.toBase` satisfying that condition, the universal property (for every $T$-point $t$ and every rigidified line bundle $M$ satisfying the condition there is a unique morphism over $t$ to $D.toBase$ with pullback of the Poincaré bundle isomorphic to $M$), and triviality of the Poincaré bundle along the zero section. It is assumed that `D.toBase` is separated.
--
--   **Smoothness off the crossings.** A hypothesis requires that every point $y$ of the special fibre `fibre (algebraMap (R p) κ)` which does not lie simultaneously in the images of the two component morphisms `𝔓.comp κ (algebraMap (R p) κ) 0` and `𝔓.comp κ (algebraMap (R p) κ) 1` has its image under `pullback.fst` contained in `𝔓.smoothLocus`.
--
--   **Special-fibre Picard data.** Properness of the base changes of `toBase N₀ p` and `toBase0 N₀ p` to $\kappa$, and smoothness of relative dimension $1$ and geometric integrality of the latter, are assumed. The hypotheses `hDκ` and `hD₀κ` assert that `D.baseChange κ` and `M.D₀.baseChange κ` represent the corresponding fibrewise-algebraically-trivial rigidified Picard functors over $\kappa$, rigidified along `sectionBaseChange κ 𝔓.εinf` and `sectionBaseChange κ M.ε₀` respectively; two further hypotheses assert that the Poincaré bundles of `hDκ` and `hD₀κ` are isomorphic to those obtained from `hD.poincare`, respectively `M.rep.poincare`, by pulling back along the first projection of the base change and transporting via `BaseChange.ofR`. The hypothesis `hε₁'` states that the base-changed section `M.ε₀` followed by `𝔓.comp κ (algebraMap (R p) κ) 0` is the base-changed section `𝔓.εinf`.
--
--   **The two abelian-quotient maps.** `abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (M.D₀.baseChange κ).toBase` is a pair of morphisms over $\mathrm{Spec}\,\kappa$ from the level-$N_0p$ to the level-$N_0$ Picard scheme of the special fibre. It is assumed that `abq 0` is the morphism `RepresentsRelSubPic.pullbackHom` determined by pullback of line bundles along `𝔓.comp κ (algebraMap (R p) κ) 0` (using `𝔓.comp_over`, `hε₁'`, `hDκ` and `hD₀κ`), and that `abq 1` satisfies the corresponding pointwise property for the second component: for every scheme $T$, every $t \colon T \to \mathrm{Spec}\,\kappa$ and every $T$-point $a$ of `(D.baseChange κ).toBase`, the pullback of the Poincaré bundle of `hD₀κ` along $a$ followed by `abq 1` is isomorphic to the `rigidify`-rigidification, along `rigSection` of the base-changed `M.ε₀` and the projection `pullback.snd`, of the pullback of `(hDκ.poincare.pullbackAlong a).L` along `curveChange` of `𝔓.comp κ (algebraMap (R p) κ) 1`.
--
--   **Generic-fibre data over $\mathbb{Q}$.** `hDQ` asserts that `D.baseChange ℚ` represents the analogous functor over $\mathbb{Q}$, `hPQ` compares its Poincaré bundle with the one obtained from `hD.poincare` by base change, and the base change of `toBase N₀ p` to $\mathbb{Q}$ is assumed separated. `ajQ` is a morphism over $\mathbb{Q}$ from the base-changed curve to `(D.baseChange ℚ).P` with `hajQε` saying that the section at infinity composed with `ajQ` is the zero section, and `hajQ` saying that `ajQ` is an Abel–Jacobi map: for every field $K$, every $t \colon \mathrm{Spec}\,K \to \mathrm{Spec}\,\mathbb{Q}$ and every $t$-point $x$ of the curve, the pullback of the Poincaré bundle along $x$ followed by `ajQ` is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor cut out by $x$ with the ideal module of the relative effective Cartier divisor cut out by $t$ followed by the section at infinity. Finally `kQ`, with `hkQ₁` and `hkQ₂`, is a comparison morphism from the fibre over the geometric generic point `genPt p` to the fibre over $\mathbb{Q}$, compatible with both projections (the second up to `specMap ℚ (AlgebraicClosure ℚ)`).
--
--   **Geometric Abel–Jacobi and the point dictionary.** `ajbar : 𝔓.Meta.C ⟶ D.P` is given, with `hajbar` identifying it with `𝔓.eeta` followed by `kQ`, by `ajQ` and by `pullback.fst`, and `hajbar_over` saying it lies over `𝔓.Meta.toBase` followed by `genPt p`. `εbar` is a section of `𝔓.Meta.toBase`, with `hεbar` placing it over the section $\mathfrak{P}.\varepsilon_{\inf}$ and `hεbar_aj` saying that `εbar` followed by `ajbar` is `genPt p` followed by the zero section of $D$. `pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase` is a bijection between the degree-zero divisor class group $\mathrm{Pic}^0$ of the level-$N_0p$ modular function field over $\overline{\mathbb{Q}}$ and the geometric generic points of $D$, assumed additive for the relative group law attached to `hD` (with the group condition `algEquivZeroGroupCut`), Galois-equivariant for $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and compatible with `ajbar` in the following sense: for all $\overline{\mathbb{Q}}$-points $x, s$ of `𝔓.Meta.C` with $s$ lying over the section at infinity, there is a degree-zero divisor $D_v$ equal to $\mathrm{(place\ of\ }x) - \mathrm{(place\ of\ }s)$ under `𝔓.Meta.pointEquivPlace` with `(pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar`.
--
--   **Arithmetic specialisation data.** `data : ModularPolynomialData p` with `hKr : KroneckerCongruence p data`, the integrality hypotheses `hα` and `hβ` for the two Hecke embeddings $\bar\alpha, \bar\beta$ at level $N_0$ and prime $p$, and $P$ a `PlaceSpecialization A p N₀ data hKr κ (IsLocalRing.residue ↥A) hα hβ`, whose specialisation map `P.sp` sends places of the level-$N_0$ function field over $\overline{\mathbb{Q}}$ to places of `modularFunctionFieldC κ N₀`. $W$ is a finite set of places of `modularFunctionFieldC κ N₀` characterised by membership in `ssPlaces p N₀ κ`, the supersingular places. Two hypotheses describe the reduction of strict points: for every $\overline{\mathbb{Q}}$-point $y$ of `𝔓.Meta.C`, every $A$-point $u$ of `toBase N₀ p` whose restriction along `barPt A` is $y$ (through `𝔓.eeta` and the first projection), every $\kappa$-point $u_\kappa$ of the special fibre reducing $u$ and splitting the second projection, and under the disjunction `P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y)`, every closed point $P_0$ (resp. $P_1$) of `(𝔓.Mfib κ (algebraMap (R p) κ)).C` whose image under `𝔓.efib` is the image of the closed point under $u_\kappa$ followed by `fibreMap0 𝔓.π` (resp. by `fibreMap 𝔓.w.hom 𝔓.w_over` and then `fibreMap0 𝔓.π`) satisfies `placeOfPoint P₀ = P.reduceFst (𝔓.Meta.pointEquivPlace y)` (resp. `placeOfPoint P₁ = P.reduceSnd (…)`), where `P.reduceFst` and `P.reduceSnd` are `P.sp` applied to the restriction of the place along $\bar\alpha$, respectively $\bar\beta$. `hE` is the equality `modularFunctionFieldC κ N₀ = modularFunctionFieldFullC κ N₀`, and a further hypothesis requires that for every `h : ReductionInputsModL A N₀` the reduction of places `placeReductionModL h` agrees with `P.sp` transported along the $\kappa$-algebra ring equivalence `IntermediateField.equivOfEq hE`.
--
--   **Toric data.** A natural number $t$ and a morphism $\tau$ over $\mathrm{Spec}\,\kappa$ from `torusScheme κ t` to `(D.baseChange κ).toBase` are given, subject to the hypothesis that for every scheme $T$, every $t' \colon T \to \mathrm{Spec}\,\kappa$ and every $T$-point $a$ of `(D.baseChange κ).toBase`, the point $a$ composed with `abq i` is the unit of the base-changed relative group law attached to `M.rep` for both $i$ if and only if $a$ factors through $\tau$, i.e. equals `y ≫ τ` for some $T$-point $y$ of the torus.
--
--   **Glued specialisation and the chosen class.** `sp` is an additive map from the inertia invariants `inertiaInvariants A (N₀ * p)` of `JZero (N₀ * p)` to `GluedPic0 κ (modularFunctionFieldC κ N₀) S`, where $S :=$ `nodePairsOfPlaces (arithFrobC p κ N₀) W` is the finite set of pairs $(w, g\cdot w)$ with $w \in W$ and $g$ the arithmetic Frobenius semilinear automorphism, and `GluedPic0` is the quotient of admissible gluing data (a pair of degree-zero divisors vanishing at the first, resp. second, place of each pair, together with a unit at each pair) by the glued principal subgroup. It is assumed that `P.IsGluedSpecialization S sp` holds: for every degree-zero divisor $D'$ whose class is inertia-invariant, every admissible gluing datum $z$ with `P.IsGoodDiv D'` and $z$ equal to `P.glueData S D'`, one has `sp ⟨Pic0.mk D', _⟩ = GluedPic0.mk S z`.
--
--   Finally, $x$ is an element of `inertiaInvariants A (N₀ * p)` whose underlying class in `JZero (N₀ * p)` satisfies `P.IsGoodClass S`, i.e. is represented by a degree-zero divisor which is good and whose gluing datum is admissible; $s$ is an $A$-point of `D.toBase` (over `Spec.map (CommRingCat.ofHom M.ρ)`) with `(pts x).1 = barPt A ≫ s.1`; $s_\kappa$ is a $\kappa$-point of `(D.baseChange κ).toBase` over the identity whose composition with `pullback.fst` is the reduction of $s$; and $r \colon \mathrm{Fin}\,2 \to$ points of `M.D₀.toBase` over `resPt A ≫ Spec.map (CommRingCat.ofHom M.ρ)` is such that, for each $i$, $(r\,i).1$ is $s_\kappa$ composed with `abq i` followed by `pullback.fst`.
--
--   **Conclusion.** Writing $e$ for the ring equivalence `(IntermediateField.equivOfEq hE).toRingEquiv` from `modularFunctionFieldC κ N₀` to `modularFunctionFieldFullC κ N₀`, which fixes $\kappa$, the pair
--   $$\bigl((\mathrm{Pic}^0\text{-}\mathrm{congr}\,e)^{-1}\bigl(\mathtt{M.toLevelData.ptsSp}^{-1}(r\,0)\bigr),\ (\mathrm{Pic}^0\text{-}\mathrm{congr}\,e)^{-1}\bigl(\mathtt{M.toLevelData.ptsSp}^{-1}(r\,1)\bigr)\bigr)$$
--   of classes in $\mathrm{Pic}^0(\kappa,\ \mathtt{modularFunctionFieldC κ N₀})$ — obtained by reading each reduced point $r\,i$ as a divisor class through the dictionary `ptsSp` and transporting it back along `Pic0.congr` for $e$ — equals `GluedPic0.toPic0Pair S (sp x)`, the pair of divisor classes of the two divisor components of the glued specialisation of $x$.
--
--   This is the coordinate half of the comparison between the reduction at $p$ of points of the level-$N_0p$ Jacobian and the glued Picard group of the Deligne–Rapoport special fibre: it asserts that the two abelian-quotient components of the reduction of a good, inertia-invariant class agree with the pair of divisor classes read off from the glued specialisation on the supersingular node pairs. It is used by [`ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization`](thm.html#ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_eq_toPic0Pair_of_isGluedSpecialization), within the analysis of the semistable reduction of $J_0(N_0p)$ at $p$ that supports the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization.lean

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

theorem ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization
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
        GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (sp x) := by sorry
