-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel
-- name    : ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/781f52c4-4619-537d-ac80-ebed9103e67d
-- title:
--   Special-fibre torus, abelian quotient and pins at level N₀p
-- statement:
--   Throughout, $N_0\ge 1$ and $p$ is a prime with $p\nmid N_0$ (`hpN₀`), $A$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ lying in its nonunits (`hA : A.LiesOverPrime p`), and $\kappa :=$ `ResidueField ↥A`, which consequently has characteristic $p$. All modular schemes occurring are taken over `Spec (R p)`, the base ring of the Igusa models, and $\kappa$ is regarded as an `R p`-algebra through `IsLocalRing.residue ↥A` composed with the structure map `M.ρ`; in addition the Hecke-module structures on `JZero (N₀ * p)` and `JZero N₀` and the algebra structures on `modularFunctionFieldFullC κ N₀` are installed inside the statement.
--
--   **Model data.** `M : JZeroNeronObjectAtP.LevelModel N₀ p A` is a level-$N_0$ model at $p$ and $A$: a ring map $\rho :$ `R p` $\to A$ compatible with $\overline{\mathbb Q}$, the Igusa scheme `IgusaScheme.igusaTo N₀ p` with a cusp section $\varepsilon_0 :=$ `M.ε₀` pinned on the chart at infinity, a designation `M.D₀` (a scheme with a zero section over `Spec (R p)`) together with `M.rep`, a representability datum for the subfunctor of rigidified relative Picard classes cut out by fibrewise algebraic equivalence to zero, an Abel–Jacobi morphism `M.aj₀`, the dictionaries `M.pts` (geometric generic points) and `M.ptsSp` (points over $\kappa$), and a curve model for the function field at level $N_0$. The hypothesis `hΛ : M.toLevelData.IsJacobian` requires of the induced level datum (with structure morphism $f :=$ `M.D₀.toBase`, group law `M.law` and the two dictionaries) that $f$ carry an abelian-scheme property bundle over `R p`, that the group law be commutative on points, that `M.pts` be additive and Galois-equivariant, that `M.ptsSp` be additive, that reduction of points agree modulo $\ell$ whenever the inputs `ReductionInputsModL A N₀` are available, and that every element of the Hecke algebra be realised by an endomorphism of $f$ respecting the group law and acting on `M.pts` by composition. Further, `M.D₀.toBase` is smooth (`hsm₀`), proper (`hpr₀`) and geometrically connected (`hgc₀`).
--
--   **Package and degeneracies.** $\mathfrak P :=$ `𝔓` is a `DRModelPackageLevel N₀ p hpN₀`: a flat, proper, integral, finitely presented model `X N₀ p` of level $N_0p$ over `Spec (R p)`, normal on affine opens, equipped with a curve model `𝔓.Meta` for `modularFunctionFieldBar (N₀ * p)` together with the isomorphism `𝔓.eeta` onto the geometric generic fibre and its Galois and chart compatibilities, smooth and geometrically integral generic fibre, cusp sections `𝔓.εinf`, `𝔓.εzero`, the forgetful morphisms `𝔓.π`, `𝔓.πw`, the Atkin–Lehner datum `𝔓.w`, the fibre components `𝔓.comp`, the fibre curve model `𝔓.Mfib` with `𝔓.efib`, and a smooth locus `𝔓.smoothLocus`. The hypothesis `hcusp` says that `𝔓.εinf` followed by `𝔓.π` is $\varepsilon_0$. Both `𝔓.π.1` and `𝔓.πw.1` are assumed finite, flat and locally of finite presentation, of constant fibre rank $p+1$ (`hrk`, `hrk_w`).
--
--   `D : RelativePic0Designation (R p) (toBase N₀ p)` is a scheme over `Spec (R p)` with a zero section, and `hD` is a representability datum: a Poincaré rigidified line bundle on `D.toBase`, lying in the fibrewise-algebraically-trivial condition, which classifies uniquely all such rigidified bundles (rigidified along `𝔓.εinf`) and is trivial along the zero section. `D.toBase` is assumed smooth, separated, quasi-compact, surjective and geometrically connected (`hsm`, `hsep`, `hqc`, `hsurj`, `hgc`).
--
--   $\delta : \mathrm{Fin}\,2 \to$ `SchemeHomOver D.toBase M.D₀.toBase` is a pair of morphisms characterised by `hδ₀` and `hδ₁`: for every scheme $T$ over `Spec (R p)` and every $T$-point $a$ of `D.toBase`, the pullback of `M.rep.poincare` along $a$ followed by $\delta_0$ (resp. $\delta_1$) is isomorphic to the rigidification along the cusp section of the rank-$(p+1)$ norm module, taken along the curve change attached to `𝔓.π` (resp. to `𝔓.πw`), of the pullback of `hD.poincare` along $a$.
--
--   **Generic-fibre block (quantified hypotheses).** `hDQ` is a representability datum for `D.baseChange ℚ` over the generic fibre with the base-changed cusp section, and `hPQ` identifies its Poincaré bundle with the base change to $\mathbb Q$ of `hD.poincare` pulled back along the first projection; the generic fibre is assumed separated. `ajQ` is a morphism from the generic-fibre curve to `(D.baseChange ℚ).toBase` sending the base-changed cusp section to the zero section (`hajQε`) and Abel–Jacobi normalised (`hajQ`): for every field $K$, every $K$-point of $\mathbb Q$ and every $K$-point $x$ of the generic-fibre curve, the pullback of the Poincaré bundle along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the cusp point. `kQ` is a morphism from the geometric generic fibre to the generic fibre compatible with the first projections (`hkQ₁`) and with the second projections up to `Spec` of $\mathbb Q \to \overline{\mathbb Q}$ (`hkQ₂`). `ajbar` is `𝔓.eeta` followed by `kQ`, by `ajQ` and by the first projection (`hajbar`), lying over `genPt p` (`hajbar_over`). `εbar` is a $\overline{\mathbb Q}$-point of `𝔓.Meta.C` lying over the cusp `𝔓.εinf` (`hεbar`) and sent by `ajbar` to the zero section (`hεbar_aj`). Finally `pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase` is a bijection from $\mathrm{Pic}^0$ of `modularFunctionFieldBar (N₀ * p)` onto the geometric generic points of `D.toBase`, subject to three further hypotheses: additivity for the relative group law determined by `hD`; Galois equivariance; and the Abel–Jacobi property that for all $\overline{\mathbb Q}$-points $x,s$ of `𝔓.Meta.C` with $s$ lying over the cusp there is a degree-zero divisor $Dv$ whose underlying divisor is $[\,\text{place of }x\,]-[\,\text{place of }s\,]$ and with `pts` of its class equal to $x$ followed by `ajbar`.
--
--   **Reduction block (quantified hypotheses).** `data : ModularPolynomialData p` with `hKr : KroneckerCongruence p data` is the modular polynomial of level $p$ satisfying the Kronecker congruence modulo $p$; `hα`, `hβ` assert integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` at level $N_0$, $p$ over $\overline{\mathbb Q}$; `P` is a `PlaceSpecialization` at $A$ for these data, in particular a map `P.sp` from places of `modularFunctionFieldBar N₀` to places of `modularFunctionFieldC κ N₀`, with the attendant order conditions on $j$ and $j_N$ and a specialisation on $\mathrm{Pic}^0$. `W` is a finite set of places of `modularFunctionFieldC κ N₀` whose members are exactly the supersingular places `ssPlaces p N₀ κ`. Two pinning hypotheses (stated in the same shape for the two degeneracies) say: for every $\overline{\mathbb Q}$-point $y$ of `𝔓.Meta.C`, every $A$-point $u$ of `toBase N₀ p` reducing to $y$ at the geometric generic point, every $\kappa$-point $u_\kappa$ of the $\kappa$-fibre whose first component is the reduction of $u$ and whose second component is the identity, under the assumption that the place attached to $y$ is strict in the first or the second sense for `P` (i.e. Frobenius on places carries `P.reduceFst` to `P.reduceSnd`, resp. `P.reduceFst` is Frobenius of `P.reduceSnd`, with the corresponding non-fixedness under Frobenius squared), and for every closed point $P_0$ of the fibre curve `𝔓.Mfib`: if `𝔓.efib` sends $P_0$ to the image of the closed point of $\kappa$ under $u_\kappa$ followed by `fibreMap0 𝔓.π` (resp. under $u_\kappa$ followed by the Atkin–Lehner fibre map and then `fibreMap0 𝔓.π`), then the place of $P_0$ in `𝔓.Mfib` is `P.reduceFst` (resp. `P.reduceSnd`) of the place of $y$; here `P.reduceFst` and `P.reduceSnd` are `P.sp` applied to the restriction of a place along `heckeAlphaBar`, resp. `heckeBetaBar`. The hypothesis `hE` asserts the equality `modularFunctionFieldC κ N₀ = modularFunctionFieldFullC κ N₀`, and a further hypothesis says that for every instance of `ReductionInputsModL A N₀` the map `placeReductionModL` is `P.sp` transported along `hE`. Finally `sp` is an additive map from the inertia invariants `inertiaInvariants A (N₀ * p)` to `GluedPic0 κ (modularFunctionFieldC κ N₀) S`, where $S :=$ `nodePairsOfPlaces (arithFrobC p κ N₀) W` is the set of node pairs obtained from $W$ by the arithmetic Frobenius semilinear automorphism, it is assumed to be a glued specialisation for `P` (so that for every good degree-zero divisor with inertia-invariant class and every admissible gluing datum equal to `P.glueData S` of that divisor, `sp` of the class is the class of the gluing datum), and every inertia-invariant class whose geometric generic point `pts` extends to a point over $A$ (`ExtendsToPlace`) is assumed to be a good class for `P`.
--
--   **Conclusion.** Write $n :=$ `Nat.card ↥(ssPlaces p N₀ κ)` and $t := n-1$ (natural subtraction). Then $0 < n$, and $(n-1)+1 =$ `W.card`. Moreover there exist: a morphism `torusFibre` from the torus `torusStr κ t` (the spectrum of the group algebra `torusCoord κ t = AddMonoidAlgebra κ (Fin t → ℤ)`) to the base change of `D.toBase` along `resPt A ≫ M.toLevelData.σA`; a pair `abqFibre : Fin 2 → …` of morphisms from that base change to the base change of `M.toLevelData.f` along the same $\kappa$-point; representability data `hDκ` for `D.baseChange κ` and `hD₀κ` for `M.D₀.baseChange κ` over $\kappa$ with the base-changed cusp sections, together with isomorphisms identifying their Poincaré bundles with the base changes to $\kappa$ of `hD.poincare` and `M.rep.poincare`; the cusp compatibility `hε₁'` stating that the base-changed section of $\varepsilon_0$ followed by `𝔓.comp κ _ 0` is the base-changed section of `𝔓.εinf`; and a pair `abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (M.D₀.baseChange κ).toBase` with `abq 0` the morphism classified by pullback along `𝔓.comp κ _ 0` and `abq 1` characterised by the property that, for every $T$ over `Spec κ` and every $T$-point $a$ of `(D.baseChange κ).toBase`, the pullback of `hD₀κ.poincare` along $a$ followed by `abq 1` is isomorphic to the rigidification along the cusp section of the pullback, along the curve change of `𝔓.comp κ _ 1`, of the pullback of `hDκ.poincare` along $a$ — such that all of the following hold.
--
--   1. `torusFibre.1` is a closed immersion.
--
--   2. `torusFibre` is multiplicative on characters: for all $\chi,\chi'$ in `WithConv (torusCoord κ t →ₐ[κ] κ)`, the torus point attached to $(\chi\chi')$`.ofConv` composed with `torusFibre` is the product, in the base-changed relative group law determined by `hD`, of the composites attached to $\chi$ and to $\chi'$.
--
--   3. Each `abqFibre i` is a homomorphism: for every $T$ over `Spec κ` and all $T$-points $x,y$ of the base-changed `D.toBase`, the product of $x$ and $y$ followed by `abqFibre i` equals the product, in the base change of `M.toLevelData.L`, of $x$ followed by `abqFibre i` and $y$ followed by `abqFibre i`.
--
--   4. The morphism into the fibre product obtained from `abqFibre 0` and `abqFibre 1` is flat.
--
--   5. That same morphism is surjective.
--
--   6. Exactness at `torusFibre`: for every $T$ over `Spec κ` and every $T$-point $x$ of the base-changed `D.toBase`, the composites of $x$ with both `abqFibre i` equal the unit of the base-changed group law on `M.toLevelData.f` if and only if $x$ factors as some $T$-point of the torus followed by `torusFibre`.
--
--   7. Equivariance: for every endomorphism $\tau$ of the $\kappa$-point `resPt A ≫ M.toLevelData.σA` over itself, every $i$ and every point $x$ of `D.toBase` over that $\kappa$-point, `fibreMap (abqFibre i)` commutes with composition by $\tau$.
--
--   8. Reducedness: with $d\kappa_i$ the underlying morphism of the fibre restriction of $\delta_i$ along `resPt A ≫ M.toLevelData.σA`, and $e_\kappa$ the underlying morphism of the unit section of the base-changed group law on `M.toLevelData.f`, the fibre product of the first projections of `pullback (dκ 0) eκ` and `pullback (dκ 1) eκ` is reduced.
--
--   9. The degeneracy dictionary: for every point $x$ of `D.toBase` over the $\kappa$-point, `M.toLevelData.ptsSp.symm` of $x$ followed by $\delta_0$ equals `ptsSp.symm (fibreMap (abqFibre 0) x)` plus `frobeniusPushforwardModL κ N₀ p` of `ptsSp.symm (fibreMap (abqFibre 1) x)`, and `ptsSp.symm` of $x$ followed by $\delta_1$ equals `frobeniusPushforwardModL κ N₀ p` of `ptsSp.symm (fibreMap (abqFibre 0) x)` plus `ptsSp.symm (fibreMap (abqFibre 1) x)`.
--
--   10. Agreement with the glued specialisation: for every inertia-invariant class $x$ in `inertiaInvariants A (N₀ * p)` and every point $s$ of `D.toBase` over `M.toLevelData.σA` with `(pts x).1 = barPt A ≫ s.1`, the pair obtained by transporting, along the inverse of the isomorphism of $\mathrm{Pic}^0$ groups induced by `hE`, the two classes `ptsSp.symm (fibreMap (abqFibre i) …)` of the restriction of $s$ to $\kappa$, equals `GluedPic0.toPic0Pair S (sp x)`, the image of `sp x` in $\mathrm{Pic}^0\times\mathrm{Pic}^0$.
--
--   11. Torus criterion for triviality: for the same $x$ and $s$, the restriction of $s$ to $\kappa$, viewed as a $\kappa$-point of the base change, factors through `torusFibre` if and only if `GluedPic0.toPic0Pair S (sp x) = 0`.
--
--   12. Compatibility of `abqFibre` with `abq`: for every $i$, every $T$ over `Spec κ`, every $T$-point $a$ of the base change along `resPt A ≫ M.toLevelData.σA` and every $T$-point $a'$ of `(D.baseChange κ).toBase` with the same image under the respective first projections, the composite of $a$ with `abqFibre i` and the composite of $a'$ with `abq i` have the same image under the respective first projections.
--
--   This is the Deligne–Rapoport/Raynaud description of the special fibre at $p$ of the relative $\mathrm{Pic}^0$ of the model of level $N_0p$: an extension of a product of two copies of the level-$N_0$ object by a torus whose character group is indexed by the supersingular points, together with the degeneracy (Eichler–Shimura) dictionary modulo $p$ and the pins matching the torus part with the glued $\mathrm{Pic}^0$ of the specialised curve. It is the strengthened form of the special-fibre step, exporting in addition the $\kappa$-representability data, the Poincaré compatibilities, the cusp lift and the identification of `abqFibre` with the pinned pair `abq`, and it is used by the constructor [`ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel) which assembles the Néron object of $J_0(N_0p)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel.lean

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
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_ModularCurve_FrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (hΛ : M.toLevelData.IsJacobian)
    (hsm₀ : Smooth M.D₀.toBase) (hpr₀ : IsProper M.D₀.toBase) (hgc₀ : GeometricallyConnected M.D₀.toBase)

    (𝔓 : DRModelPackageLevel N₀ p hpN₀) (hcusp : 𝔓.εinf.1 ≫ 𝔓.π.1 = M.ε₀.1)

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)
    [IsFinite 𝔓.πw.1] [Flat 𝔓.πw.1] [LocallyOfFinitePresentation 𝔓.πw.1] (hrk_w : ∀ x, 𝔓.πw.1.finrank x = p + 1)
    (δ : Fin 2 → SchemeHomOver D.toBase M.D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L))) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra
    ∀
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

      (sp : ↥(inertiaInvariants A (N₀ * p)) →+
        GluedPic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))
      (_ : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) sp)

      (_ : ∀ x : ↥(inertiaInvariants A (N₀ * p)),
        ExtendsToPlace A M.toLevelData.σA (pts (x : JZero (N₀ * p))) →
          P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (x : JZero (N₀ * p))),

    0 < Nat.card ↥(ssPlaces p N₀ (ResidueField ↥A)) ∧
    (Nat.card ↥(ssPlaces p N₀ (ResidueField ↥A)) - 1) + 1 = W.card ∧
    ∃ (torusFibre : SchemeHomOver (torusStr (ResidueField ↥A) (Nat.card ↥(ssPlaces p N₀ (ResidueField ↥A)) - 1))
        (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) D.toBase))
      (abqFibre : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) D.toBase)
        (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) M.toLevelData.f))

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
                (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) t)).obj (hDκ.poincare.pullbackAlong a).L))),

      IsClosedImmersion torusFibre.1 ∧

      (∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) (Nat.card ↥(ssPlaces p N₀ (ResidueField ↥A)) - 1) →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) torusFibre =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ M.toLevelData.σA)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) torusFibre)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) torusFibre)) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) D.toBase)),
      NeronModelInfra.schemeHomOverComp (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ M.toLevelData.σA)).mul s x y) (abqFibre i) =
        (M.toLevelData.L.baseChange (resPt A ≫ M.toLevelData.σA)).mul s (NeronModelInfra.schemeHomOverComp x (abqFibre i))
          (NeronModelInfra.schemeHomOverComp y (abqFibre i))) ∧

      Flat (pullback.lift (abqFibre 0).1 (abqFibre 1).1 ((abqFibre 0).2.trans (abqFibre 1).2.symm)) ∧

      Surjective (pullback.lift (abqFibre 0).1 (abqFibre 1).1 ((abqFibre 0).2.trans (abqFibre 1).2.symm)) ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) D.toBase)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abqFibre i) = (M.toLevelData.L.baseChange (resPt A ≫ M.toLevelData.σA)).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) (Nat.card ↥(ssPlaces p N₀ (ResidueField ↥A)) - 1)),
          NeronModelInfra.schemeHomOverComp y torusFibre = x) ∧

      (∀ (τ : SchemeHomOver (resPt A ≫ M.toLevelData.σA) (resPt A ≫ M.toLevelData.σA)) (i : Fin 2)
      (x : SchemeHomOver (resPt A ≫ M.toLevelData.σA) D.toBase),
      fibreMap (abqFibre i) (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 x) =
        GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (fibreMap (abqFibre i) x)) ∧

      (let dκ := fun i : Fin 2 =>
      (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ M.toLevelData.σA) M.toLevelData.f D.toBase (δ i)).1
    let eκ := ((M.toLevelData.L.baseChange (resPt A ≫ M.toLevelData.σA)).one (𝟙 _)).1
    AlgebraicGeometry.IsReduced (pullback (pullback.fst (dκ 0) eκ) (pullback.fst (dκ 1) eκ))) ∧

      (∀ x : SchemeHomOver (resPt A ≫ M.toLevelData.σA) D.toBase,
        M.toLevelData.ptsSp.symm (NeronModelInfra.schemeHomOverComp x (δ 0)) =
            M.toLevelData.ptsSp.symm (fibreMap (abqFibre 0) x) +
              frobeniusPushforwardModL (ResidueField ↥A) N₀ p (M.toLevelData.ptsSp.symm (fibreMap (abqFibre 1) x)) ∧
        M.toLevelData.ptsSp.symm (NeronModelInfra.schemeHomOverComp x (δ 1)) =
            frobeniusPushforwardModL (ResidueField ↥A) N₀ p (M.toLevelData.ptsSp.symm (fibreMap (abqFibre 0) x)) +
              M.toLevelData.ptsSp.symm (fibreMap (abqFibre 1) x)) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver M.toLevelData.σA D.toBase),
          (pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (M.toLevelData.ptsSp.symm (fibreMap (abqFibre 0) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ M.toLevelData.σA) M.toLevelData.σA) s))),
            (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (M.toLevelData.ptsSp.symm (fibreMap (abqFibre 1) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ M.toLevelData.σA) M.toLevelData.σA) s)))) =
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (sp x)) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver M.toLevelData.σA D.toBase),
          (pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) (Nat.card ↥(ssPlaces p N₀ (ResidueField ↥A)) - 1)),
              NeronModelInfra.schemeHomOverComp y torusFibre = toFibrePt (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ M.toLevelData.σA) M.toLevelData.σA) s)) ↔
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (sp x) = 0)) ∧

        (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
          (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ M.toLevelData.σA) D.toBase))
          (a' : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
          a'.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = a.1 ≫ pullback.fst D.toBase (resPt A ≫ M.toLevelData.σA) →
          (NeronModelInfra.schemeHomOverComp a (abqFibre i)).1 ≫ pullback.fst M.toLevelData.f (resPt A ≫ M.toLevelData.σA) =
            (NeronModelInfra.schemeHomOverComp a' (abq i)).1 ≫ pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A))) := by sorry
