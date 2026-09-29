-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel
-- name    : ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/c8c98eb2-b1cb-5f67-b141-0c2cc202e6f3
-- title:
--   Néron object of J₀(N₀p) at p from a level model
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$ (hypothesis `hpN₀`), and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, i.e. the image of $p$ lies in the non-units of $A$; write $\kappa_A =$ `ResidueField ↥A`, a field of characteristic $p$ by [`ValuationSubring.charP_residueField_of_liesOverPrime_def`](def/WeierstrassCurve_ReductionMap.html#L57). All schemes live over the $p$-local base ring denoted `R p` (the same ring as `baseRing p`), with `base p = Spec (CommRingCat.of (baseRing p))`.
--
--   The first datum is a level-$N_0$ model `M : JZeroNeronObjectAtP.LevelModel N₀ p A`: a ring map `M.ρ : baseRing p →+* ↥A` compatible with the algebra map into $\overline{\mathbb{Q}}$, properness of the Igusa morphism `IgusaScheme.igusaTo N₀ p`, a cusp chart `M.φinf` pinned by its constant $q$-expansion coefficients, the cusp section `M.ε₀` factoring through that chart, a pointed scheme `M.D₀ : RelativePic0Designation (baseRing p) (IgusaScheme.igusaTo N₀ p)` together with `M.rep`, the assertion that `M.D₀` represents the functor of line bundles on the level-$N_0$ curve rigidified along `M.ε₀` and satisfying the fibrewise condition `algEquivZeroCut` (pullback to each geometric fibre is algebraically equivalent to zero), an Abel–Jacobi morphism `M.aj₀` sending the cusp to the zero section and realising, on $K$-points, the class of the divisor $x-\infty$, dictionaries `M.pts : JZero N₀ ≃ SchemeHomOver (genPt p) M.D₀.toBase` and `M.ptsSp` over $\kappa_A$, and a curve model `M.Meta₀` of `modularFunctionFieldBar N₀` with its identification `M.eeta₀` of the geometric generic fibre (the remaining fields of the structure are summarised here).
--
--   Three further hypotheses concern this model. `hΛ : M.toLevelData.IsJacobian` requires, for the level datum $\Lambda$ obtained from `M` (structure morphism $\Lambda.f =$ `M.D₀.toBase`, group law $\Lambda.L$, dictionaries $\Lambda.\mathrm{pts}$, $\Lambda.\mathrm{ptsSp}$): that $\Lambda.f$ carries an `AbelianSchemePropertyBundle` over `baseRing p`; that $\Lambda.L$ is commutative on points over every base; that $\Lambda.\mathrm{pts}$ is additive and Galois-equivariant, the Galois action on points being induced by $\operatorname{Spec}$ of the automorphism of $\overline{\mathbb{Q}}$; that $\Lambda.\mathrm{ptsSp}$ is additive; that, whenever `ReductionInputsModL A N₀` holds, reduction of points agrees with $\Lambda.\mathrm{ptsSp}$; and that every element of the Hecke algebra is realised by an endomorphism of $\Lambda.f$ compatible with the group law and with $\Lambda.\mathrm{pts}$. The hypotheses `hsm₀`, `hpr₀`, `hgc₀` state that `M.D₀.toBase` is smooth, proper and geometrically connected.
--
--   The second datum is `𝔓 : DRModelPackageLevel N₀ p hpN₀`, a Deligne–Rapoport model package for the level-$N_0p$ curve `toBase N₀ p` over `R p`: the structure morphism is proper, flat and locally of finite presentation with integral source, affine charts have integrally closed sections, `𝔓.Meta` is a curve model of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb{Q}}$ identified by the isomorphism `𝔓.eeta` with the geometric generic fibre, compatibly with the arithmetic Galois action (`𝔓.hgal`) and with the $q$-expansion charts (`𝔓.Meta_pin`), the generic fibre is smooth of relative dimension $1$ and geometrically integral, and the package carries the cusp sections `𝔓.εinf`, `𝔓.εzero`, the forgetful morphism `𝔓.π` to the level-$N_0$ curve, the Atkin–Lehner data `𝔓.w`, `𝔓.πw`, the component morphisms `𝔓.comp` of the fibres over residue-field points with their compatibilities `𝔓.comp_over`, and the fibre curve models `𝔓.Mfib` with the morphisms `𝔓.efib` (the remaining fields are summarised here). The last hypothesis `hcusp` couples the two data: `𝔓.εinf.1 ≫ 𝔓.π.1 = M.ε₀.1`, i.e. the forgetful morphism carries the cusp $\infty$ of the package to the cusp section of the model.
--
--   The conclusion asserts the existence of `O : JZeroNeronObjectAtP N₀ p hpN₀ A hA M.toLevelData` — a scheme `O.G` with structure morphism `O.g : O.G ⟶ base p` which is smooth, separated, locally of finite type, quasi-compact, surjective with preconnected fibres, a commutative relative group law `O.L`, a bijection `O.pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) O.g` that is additive, Galois-equivariant and Hecke-equivariant through endomorphisms of `O.g`, flatness and surjectivity of multiplication by every $n>0$, properness of the generic fibre, a toric rank `O.toricRank` and the remaining special-fibre dévissage data — satisfying four groups of assertions. Throughout, $D$ denotes the pointed scheme `RelativePic0Designation (R p) (toBase N₀ p)` with total space `O.G`, structure morphism `O.g` and zero section the unit of `O.L`, and $\kappa_A$ is made an `R p`-algebra through `IsLocalRing.residue ↥A` composed with `M.ρ`.
--
--   First group. There exist: `hD`, asserting that $D$ represents the relative Picard functor of `toBase N₀ p` rigidified along `𝔓.εinf` and cut out by `algEquivZeroCut`; the corresponding representability `hDQ` after base change to $\mathbb{Q}$, by `D.baseChange ℚ`, with `hPQ` an isomorphism between its Poincaré bundle and the base change from `R p` of the pullback of the Poincaré bundle of `hD` along the first projection; the same data `hDκ` over $\kappa_A$ together with the analogous isomorphism of Poincaré bundles; the representability `hD₀κ` of the relative Picard functor of the base-changed level-$N_0$ curve over $\kappa_A$, rigidified along the base change of `M.ε₀`, by `M.D₀.baseChange (ResidueField ↥A)`, together with the analogous comparison of its Poincaré bundle with the one of `M.rep`; the identity `hε₁'` saying that the base-changed cusp section `M.ε₀` followed by the $0$-th component morphism `𝔓.comp` over $\kappa_A$ is the base-changed section `𝔓.εinf`; a pair `abq : Fin 2 → SchemeHomOver (D.baseChange (ResidueField ↥A)).toBase (M.D₀.baseChange (ResidueField ↥A)).toBase` of morphisms to the level-$N_0$ Picard scheme over $\kappa_A$, with `abq 0` equal to `RepresentsRelSubPic.pullbackHom` of the $0$-th component morphism (pullback of line bundles along it), and `abq 1` characterised by the property that for every $T$, every $t : T ⟶ \operatorname{Spec} \kappa_A$ and every point $a$ of `(D.baseChange (ResidueField ↥A)).toBase` over $t$, the pullback of the Poincaré bundle of `hD₀κ` along $a$ followed by `abq 1` is isomorphic to the `Scheme.Modules.rigidify` of the pullback, along the curve change attached to the first component morphism `𝔓.comp … 1`, of the pullback of the Poincaré bundle of `hDκ` along $a$; separatedness of the generic fibre `baseChange (R p) (toBase N₀ p) ℚ`; an Abel–Jacobi morphism `ajQ` over $\mathbb{Q}$ with `hajQε` sending the cusp section to the zero section and `hajQ` identifying, for every field $K$, every $K$-point $t$ of $\operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the curve, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by `ajQ` with the tensor product of the line bundle of the relative effective Cartier divisor of $x$ and the ideal module of the divisor of the cusp; a morphism `kQ` from the geometric generic fibre to the fibre over $\mathbb{Q}$ with the two compatibilities `hkQ₁`, `hkQ₂` over the curve and over $\operatorname{Spec}\mathbb{Q} ← \operatorname{Spec}\overline{\mathbb{Q}}$; a morphism `ajbar : 𝔓.Meta.C ⟶ D.P` equal to `𝔓.eeta` followed by `kQ`, by `ajQ` and by the first projection (`hajbar`), lying over `genPt p` (`hajbar_over`); and a section `εbar` of `𝔓.Meta.toBase` mapping to the cusp `𝔓.εinf` in the geometric generic fibre (`hεbar`) and to the zero section under `ajbar` (`hεbar_aj`). For these, four statements hold: (a) `O.pts` is additive for the group law `RepresentsRelSubPic.relativeGroupLaw` attached to `hD` through `algEquivZeroGroupCut`; (b) for all sections $x, s$ of `𝔓.Meta.toBase` such that $s$ maps to the cusp `𝔓.εinf`, there is a degree-zero divisor $Dv$ on `modularFunctionFieldBar (N₀ * p)` equal to the difference of the single divisors at the places `𝔓.Meta.pointEquivPlace x` and `𝔓.Meta.pointEquivPlace s`, whose class satisfies $(O.\mathrm{pts}(\mathrm{Pic}^0.\mathrm{mk}\,Dv)).1 = x.1 \mathbin{≫} \mathrm{ajbar}$; (c) for each $i \in \{0,1\}$, each $t : T ⟶ \operatorname{Spec}\kappa_A$ and each pair of points $a$ of the base change of `O.g` along `resPt A ≫ M.toLevelData.σA` and $a'$ of `(D.baseChange (ResidueField ↥A)).toBase` whose underlying morphisms into the curve agree, the points obtained by composing $a$ with `O.abqFibre i` and $a'$ with `abq i` have equal underlying morphisms into the level-$N_0$ Picard scheme; (d) in the same situation, the composites of $a'$ with `abq 0` and `abq 1` are both the unit of the base-changed group law of `M.rep` if and only if $a$ lifts to a point of the torus `torusStr (ResidueField ↥A) O.toricRank` through `O.torusFibre`.
--
--   Second group. There exist: modular polynomial data `data : ModularPolynomialData p` (a monic $\Phi$ of degree $\psi(p)$ vanishing on the pair of $q$-expansions) satisfying the Kronecker congruence `hKr`; integrality `hα`, `hβ` of the two Hecke degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` over $\overline{\mathbb{Q}}$ at level $N_0$ and prime $p$; a place specialization `P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ`, carrying a map `P.sp` from places of `modularFunctionFieldBar N₀` to places of `modularFunctionFieldC (ResidueField ↥A) N₀`, a homomorphism `P.spPic0` on divisor classes, and the order-compatibility axioms for $j$ and $j_N$; a prolongation tuple `Rt : PlaceSpecialization.ProlongationTuple P` (a residue map $\kappa_A → \kappa_A$-compatible embedding `Rt.ι` and two regular prolongations `Rt.R₁`, `Rt.R₂` of $A$ to the level-$N_0p$ function field, exchanged by the Atkin–Lehner involution) satisfying `Rt.IsModel` (the two divisor laws and the two cusp laws), `Rt.RegularityLaw O.ssFinset`, `Rt.NodeValueLaw O.ssFinset` and `Rt.OrderLawFixed`; a homomorphism `sp` from the inertia invariants `inertiaInvariants A (N₀ * p)` of $J_0(N_0p)$ to `GluedPic0` of `modularFunctionFieldC (ResidueField ↥A) N₀` for the finite set of node pairs obtained from `O.ssFinset` by `nodePairsOfPlaces` for the arithmetic Frobenius `arithFrobC p (ResidueField ↥A) N₀`, satisfying `P.IsGluedSpecialization` for that set; and an equality `hE` of the two intermediate fields `modularFunctionFieldC (ResidueField ↥A) N₀` and `modularFunctionFieldFullC (ResidueField ↥A) N₀`. For these, six statements hold: `O.frob = arithFrobC p (ResidueField ↥A) N₀`; for every section $y$ of `𝔓.Meta.toBase`, every $A$-point $u$ of the curve lifting $y$, every $\kappa_A$-point `uκ` of the fibre reducing $u$ and splitting the projection, and under the assumption that `P.IsStrictFst` or `P.IsStrictSnd` holds at the place of $y$, any closed point `P0` of `𝔓.Mfib` whose image under `𝔓.efib` is the image of the closed point under `uκ` followed by `fibreMap0 𝔓.π` has place equal to `P.reduceFst` of the place of $y$; the same statement with `fibreMap 𝔓.w.hom` inserted before `fibreMap0 𝔓.π` and `P.reduceSnd` on the right; for $x$ in the inertia invariants, the $\overline{\mathbb{Q}}$-point `O.pts x` extends to a point over `M.toLevelData.σA` if and only if `P.IsGoodClass` holds for $x$ and the above set of node pairs; for $x$ in the inertia invariants and $s$ a point of `O.g` over `M.toLevelData.σA` with $(O.\mathrm{pts}\,x).1 = \mathrm{barPt}\,A \mathbin{≫} s.1$, the pair of divisor classes obtained by reducing $s$ to the special fibre, composing with `O.abqFibre 0` and `O.abqFibre 1`, reading the result through the inverse of `M.toLevelData.ptsSp` and transporting along `hE` by `Pic0.congr`, equals `GluedPic0.toPic0Pair` of `sp x`; and, in the same situation, the reduced point of $s$ lifts through `O.torusFibre` to a point of the torus `torusStr (ResidueField ↥A) O.toricRank` if and only if `GluedPic0.toPic0Pair (sp x) = 0`.
--
--   Third group: for every $m$ coprime to $p$, every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` and every $m$-torsion class $x$ in `jZeroTorsion (N₀ * p) m`, the difference $\sigma \cdot x - x$ lies in `O.toricPts m`, the subgroup generated by the toric points. Fourth group: for every $m > 0$, every $\sigma$ in the same inertia subgroup and every $x$ in `jZeroTorsion (N₀ * p) m`, the difference $\sigma \cdot x - x$ lies in `O.finPts m`, the subgroup generated by the $m$-torsion classes whose points extend over $A$.
--
--   This is the constructor of the Néron-type object at $p$ for $J_0(N_0p)$ out of a level-$N_0$ Jacobian model and a Deligne–Rapoport model package, together with all the bridges relating its points, its Abel–Jacobi pin, its special-fibre degeneracy and toric data, and the specialization of divisor classes to the glued Picard group of the two copies of the level-$N_0$ curve in characteristic $p$. It is cited by [`ModularCurve.exists_jZeroNeronObjectAtP_and_bridge`](thm.html#ModularCurve.exists_jZeroNeronObjectAtP_and_bridge), and its last two clauses are the inertia statements used in the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel.lean

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
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (hΛ : M.toLevelData.IsJacobian)
    (hsm₀ : Smooth M.D₀.toBase) (hpr₀ : IsProper M.D₀.toBase) (hgc₀ : GeometricallyConnected M.D₀.toBase)

    (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (hcusp : 𝔓.εinf.1 ≫ 𝔓.π.1 = M.ε₀.1) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra
    ∃ (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA M.toLevelData),

      (letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
        let D : RelativePic0Designation (R p) (toBase N₀ p) :=
          ⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩
        ∃ (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
        (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
            (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
        (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
            (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

        (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)) (D.baseChange (ResidueField ↥A)))
        (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A)
          (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
        (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
          (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) (M.D₀.baseChange (ResidueField ↥A)))
        (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
          (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
        (hε₁' : (sectionBaseChange (ResidueField ↥A) M.ε₀).1 ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0 =
          (sectionBaseChange (ResidueField ↥A) 𝔓.εinf).1)

        (abq : Fin 2 → SchemeHomOver (D.baseChange (ResidueField ↥A)).toBase (M.D₀.baseChange (ResidueField ↥A)).toBase)
        (_ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
          (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) hε₁' hDκ hD₀κ)
        (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
          Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
            Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t (sectionBaseChange (ResidueField ↥A) M.ε₀))
                (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t)
              ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)
                (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) t)).obj (hDκ.poincare.pullbackAlong a).L)))

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
        (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection),

        (∀ x y : JZero (N₀ * p),
          O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧
        (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
          s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
              Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
            (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) ∧

        (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
          (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) O.g))
          (a' : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
          a'.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = a.1 ≫ pullback.fst O.g (resPt A ≫ M.toLevelData.σA) →
          (NeronModelInfra.schemeHomOverComp a (O.abqFibre i)).1 ≫ pullback.fst M.toLevelData.f (resPt A ≫ M.toLevelData.σA) =
            (NeronModelInfra.schemeHomOverComp a' (abq i)).1 ≫ pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A))) ∧

        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
          (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) O.g))
          (a' : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
          a'.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = a.1 ≫ pullback.fst O.g (resPt A ≫ M.toLevelData.σA) →
          ((∀ i, NeronModelInfra.schemeHomOverComp a' (abq i) =
              ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) M.rep).baseChange (specMap (R p) (ResidueField ↥A))).one t) ↔
            ∃ y : SchemeHomOver t (torusStr (ResidueField ↥A) O.toricRank), NeronModelInfra.schemeHomOverComp y O.torusFibre = a))) ∧

      (∃ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
          (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
          (Rt : PlaceSpecialization.ProlongationTuple P) (_ : Rt.IsModel) (_ : Rt.RegularityLaw O.ssFinset)
          (_ : Rt.NodeValueLaw O.ssFinset) (_ : Rt.OrderLawFixed)
          (sp : ↥(inertiaInvariants A (N₀ * p)) →+
            GluedPic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset))
          (_ : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) sp)

          (hE : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀),

        O.frob = arithFrobC p (ResidueField ↥A) N₀ ∧

        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp M.ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ)).base P0.1 =
                (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp M.ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y)) ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp M.ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ)).base P1.1 =
                (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp M.ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp M.ρ)).base
                  (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y)) ∧

        (∀ x : ↥(inertiaInvariants A (N₀ * p)),
          ExtendsToPlace A M.toLevelData.σA (O.pts (x : JZero (N₀ * p))) ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (x : JZero (N₀ * p))) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver M.toLevelData.σA O.g),
          (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (M.toLevelData.ptsSp.symm (fibreMap (O.abqFibre 0) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ M.toLevelData.σA) M.toLevelData.σA) s))),
            (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (M.toLevelData.ptsSp.symm (fibreMap (O.abqFibre 1) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ M.toLevelData.σA) M.toLevelData.σA) s)))) =
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (sp x)) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver M.toLevelData.σA O.g),
          (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
              NeronModelInfra.schemeHomOverComp y O.torusFibre = toFibrePt (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ M.toLevelData.σA) M.toLevelData.σA) s)) ↔
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (sp x) = 0))) ∧

      (∀ (m : ℕ), m.Coprime p →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.toricPts m) ∧
      (∀ (m : ℕ), 0 < m →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.finPts m) := by sorry
