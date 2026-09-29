-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/6dd25059-3cbd-5345-b93b-8c5d7cbfef77
-- title:
--   Picard–Lefschetz bundle for inertia displacement at a crossing
-- statement:
--   Arithmetic setting. Fix a prime $p$ and $M \in \mathbb{N}$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ given by `hK` as [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the $L$-base change of the function field of $X_1(Mp)$. Let $A$ be a discrete valuation domain with $L$ as fraction field, with $p$ in the maximal ideal of $A$ (`hAp`) and $\zeta$ in the image of $A$ (`hζA`), and with an $A$-algebra structure on $K$ compatible with $L$. Let $j \in K$ be the element whose Laurent expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) (`hj`), assumed nonzero; the relevant scheme is the two-chart model [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252), a morphism $X \to \operatorname{Spec} A$, assumed proper.
--
--   Special fibre. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and write $X_k$ for `pullback (ModularCurve.TwoChart.modelTo A ↥K j) (specMap A k)` with structure morphism `baseChange A (ModularCurve.TwoChart.modelTo A ↥K j) k = pullback.snd`. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be morphisms $C_1 \to X_k$, $C_2 \to X_k$ over $\operatorname{Spec} k$ (elements of `SchemeHomOver`, i.e. morphisms together with the identity of their composite with the structure morphism of $X_k$ with $c_1$, resp. $c_2$), each a closed immersion. The hypothesis `hcover` says that every point of $X_k$ lies in the image of $i_1$ or of $i_2$; `hred` says that `pullback i₁.1 i₂.1` is reduced, and `hn`, `hn0` say that its number of points is a natural number $n > 0$.
--
--   Sections. $\varepsilon$ is a section of $X \to \operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ are sections of $c_1$, $c_2$; the hypothesis `hε₁` says that $\varepsilon_1$ followed by $i_1$ is the base change `sectionBaseChange k ε` of $\varepsilon$.
--
--   Relative Picard data. $D$ is a `RelativePic0Designation` for $X \to \operatorname{Spec} A$, that is a scheme `D.P` with a morphism `D.toBase` to $\operatorname{Spec} A$ and a section `D.zeroSection` of it; `hrep` asserts that $D$ represents, with $\varepsilon$ as rigidifying section, the subfunctor of the relative Picard functor cut out by `algEquivZeroCut` (fibrewise algebraic equivalence to zero of rigidified line bundles): there is a Poincaré rigidified line bundle on the pullback of $X$ along `D.toBase` satisfying the cut, every rigidified line bundle over a base $T$ satisfying the cut is the pullback of the Poincaré bundle along a unique $T$-point of `D.toBase`, and the zero section pulls it back to the unit. Further, `D.toBase` is smooth (`hsm`) and separated (`hsep`); `hreps` is the corresponding representability statement for the base change `D.baseChange k` relative to $X_k$ and `sectionBaseChange k ε`, and `hPk` asserts an isomorphism between the Poincaré bundle of `hreps` and the $k$-base change (`BaseChange.ofR`) of the pullback of the Poincaré bundle of `hrep` along `pullback.fst D.toBase (specMap A k)`. Likewise $D_1$, $D_2$ are `RelativePic0Designation`s for $c_1$, $c_2$, represented with sections $\varepsilon_1$, $\varepsilon_2$ (`hrep₁`, `hrep₂`). The morphism $\nu_2$ from `(D.baseChange k).toBase` to `D₂.toBase` over $\operatorname{Spec} k$ satisfies `hν₂`: for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of `(D.baseChange k).toBase`, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the `rigidify` (tensoring with the pullback of the dual of the restriction along the rigidifying section) of the pullback along `curveChange i₂.1 i₂.2 t` of the pullback of the Poincaré bundle of `hreps` along $a$.
--
--   Generic fibre as a curve model. Fixing $A$- and $L$-algebra structures on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` in a tower, $M_\eta$ is a `CurveModel` over $\overline{\mathbb{Q}}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (an integral scheme, proper and smooth of relative dimension $1$ over $\overline{\mathbb{Q}}$, with a ring isomorphism from the function field extension to its scheme-theoretic function field compatible with the base, a bijection between its closed points and the places, the compatibility of stalks with valuation subrings, and the property that finitely many points lie in a common affine open). The morphism $e_\eta$ from `Mη.C` to `pullback (modelTo) (specMap A (AlgebraicClosure ℚ))` is an isomorphism compatible with the structure morphisms (`heη`). The instance `Mη_chart_nonempty` says the preimage under $e_\eta$ followed by `pullback.fst` of the image of the finite chart [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231) is nonempty; `hMηpin` says that for each element $a$ of the finite chart algebra `chartAlgFin A ↥K j` the germ of the pulled-back section at that open corresponds, under `Mη.ffEquiv.symm`, to the Laurent series obtained from $a$ by applying [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) to the structure map $L \to \overline{\mathbb{Q}}$. The hypothesis `hgal` asserts Galois equivariance: for every $g \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of `Mη.C`, if $x'$ followed by $e_\eta$ and `pullback.fst` equals $\operatorname{Spec}(g)$ followed by the same composite for $x$, then `Mη.pointEquivPlace x'` is the image of `Mη.pointEquivPlace x` under the action of [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   Special-fibre group bookkeeping. $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), i.e. abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s` and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $\operatorname{Spec} k$-points of `(D.baseChange k).toBase`, `D₁.toBase`, `D₂.toBase`; the hypotheses `hadd`, `haddI`, `haddE` say that in each case addition corresponds to tensor product of the pullbacks of the respective Poincaré bundles, and `hproj` says that for every $x$ the first component of `G.proj x` corresponds to $x$ composed with the morphism `RepresentsRelSubPic.pullbackHom` induced by $i_1$ and `hε₁`, and the second component to $x$ composed with $\nu_2$. Moreover $w$ is an `IntegralWeightOneForm k M` (a weight-one modular form for $\Gamma_1(M)$ with an integral $q$-expansion whose reduction over $k$ is nonzero), and $C_1$, $C_2$ are realised as curve models over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) by isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$ and $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`).
--
--   Abel–Jacobi data. A bijection `gpts` identifies [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group $\operatorname{Pic}^0(\overline{\mathbb{Q}}, \mathrm{x1FunctionFieldBar}\,(M * p))$, with the $\overline{\mathbb{Q}}$-points of `D.toBase`, and `hgadd` says it is additive for the relative group law coming from `hrep` and `algEquivZeroGroupCut`. Over $L$: `hDL` is the representability statement for the $L$-base change of $X$ with section `sectionBaseChange L ε` and designation `D.baseChange L`; $\mathrm{aj}_L$ is a morphism from $X_L$ to `(D.baseChange L).toBase` over $\operatorname{Spec} L$; $k_L$ is a morphism from $X_{\overline{\mathbb{Q}}}$ to $X_L$ compatible with both projections (`hkL₁`, `hkL₂`); $\overline{\mathrm{aj}}$ is a morphism from `Mη.C` to `D.P`; $\overline{\varepsilon}$ is a $\overline{\mathbb{Q}}$-point of `Mη.C`. The hypotheses are: `hPL`, the analogue of `hPk` over $L$; `hajLε`, that the base-changed $\varepsilon$ followed by $\mathrm{aj}_L$ is the zero section of `D.baseChange L`; `hajL`, that for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $t$-point $x$ of $X_L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{aj}_L$ is isomorphic to the tensor product of the `lineBundle` of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` of $x$ with the `idealModule` of that of $t$ followed by the base-changed $\varepsilon$; `hajbar`, that $\overline{\mathrm{aj}}$ is $e_\eta$ followed by $k_L$, $\mathrm{aj}_L$ and `pullback.fst D.toBase (specMap A L)`; `hajbar_over`, the compatibility of $\overline{\mathrm{aj}}$ with the structure morphisms; `hεbar`, that $\overline{\varepsilon}$ followed by $e_\eta$ and `pullback.fst` is `specMap A (AlgebraicClosure ℚ)` followed by $\varepsilon$; `hεbar_aj`, that $\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ is `specMap A (AlgebraicClosure ℚ)` followed by `D.zeroSection`; and `hpts_aj`, that for all $\overline{\mathbb{Q}}$-points $x, s$ of `Mη.C` with $s$ inducing the base-changed $\varepsilon$, there is a degree-zero divisor $D_v$ on `x1FunctionFieldBar (M * p)` equal to $\mathrm{single}(\text{place of } x) - \mathrm{single}(\text{place of } s)$ with `gpts (Pic0.mk Dv)` equal to $x$ followed by $\overline{\mathrm{aj}}$.
--
--   The place, the inertia element and the crossing point. $Pl$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $Pl$ (`hPl`), $\rho : A \to Pl$ a ring homomorphism whose composite with the inclusion of $Pl$ is the structure map $A \to \overline{\mathbb{Q}}$ (`hρ`), and $\pi_k : Pl \to k$ a surjective ring homomorphism with $\pi_k \circ \rho$ the structure map $A \to k$ (`hAlgk`, `hπk`). Let $\sigma$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ lying in `Pl.inertiaSubgroupIn ℚ` (the image in the decomposition subgroup of the inertia subgroup) and fixing $L$ pointwise (`hσL`). Let $P, P'$ be $\overline{\mathbb{Q}}$-points of `Mη.C` such that $P'$ followed by $e_\eta$ and `pullback.fst` equals $\operatorname{Spec}(\sigma)$ followed by the same composite for $P$ (`hP'`): thus $P'$ is the $\sigma$-translate of $P$. Let $Pt$ be a $Pl$-point of $X$ over `Spec.map (CommRingCat.ofHom ρ)` with $P$ followed by $e_\eta$ and `pullback.fst` equal to $\operatorname{Spec}$ of the inclusion of $Pl$ followed by $Pt$ (`hPt`): $Pt$ extends $P$ over $Pl$. Let $u_\kappa : \operatorname{Spec} k \to X_k$ satisfy `huκ'`, that $u_\kappa$ followed by `pullback.fst` is $\operatorname{Spec}(\pi_k)$ followed by $Pt$, and `huκ`, that $u_\kappa$ is a section of $X_k \to \operatorname{Spec} k$. Finally $\nu$ is a point of `pullback i₁.1 i₂.1` with `hν`: the image of the closed point of $\operatorname{Spec} k$ under $u_\kappa$ is the image of $\nu$ under `pullback.fst i₁.1 i₂.1` followed by $i_1$, so the reduction of $Pt$ is the crossing point $\nu$. The comparison morphisms $j_\eta$ from $X_{\overline{\mathbb{Q}}}$ and $j_k$ from $X_k$ to `pullback (modelTo) (Spec.map (CommRingCat.ofHom ρ))` are required to respect the first projections (`hjη₁`, `hjk₁`) and to respect the second projections after composing with $\operatorname{Spec}$ of the inclusion of $Pl$, respectively of $\pi_k$ (`hjη₂`, `hjk₂`).
--
--   Conclusion. There exists a module $\mathcal{M}$ on `pullback (ModularCurve.TwoChart.modelTo A ↥K j) (Spec.map (CommRingCat.ofHom ρ))`, the model base-changed to $Pl$, such that:
--
--   (i) $\mathcal{M}$ satisfies `Scheme.Modules.IsInvertible`, i.e. every point has an open neighbourhood on which the restriction of $\mathcal{M}$ is isomorphic to the unit module;
--
--   (ii) the pullback of $\mathcal{M}$ along $j_\eta$ is isomorphic to the tensor product of the `lineBundle` of the degree-one relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to the $\overline{\mathbb{Q}}$-point $P'$ followed by $e_\eta$ and `pullback.fst`, with the `idealModule` of the one attached to $P$ followed by the same composite, that is to $\mathcal{O}(P') \otimes \mathcal{O}(-P)$ on $X_{\overline{\mathbb{Q}}}$;
--
--   (iii) the pullback of $\mathcal{M}$ along $i_1$ followed by $j_k$ is isomorphic to the unit module `SheafOfModules.unit C₁.ringCatSheaf` on $C_1$;
--
--   (iv) the pullback of $\mathcal{M}$ along $i_2$ followed by $j_k$ is isomorphic to the unit module `SheafOfModules.unit C₂.ringCatSheaf` on $C_2$.
--
--   Each of (ii)–(iv) is asserted as the nonemptiness of the corresponding type of isomorphisms.
--
--   This is the Picard–Lefschetz step for the two-chart model of $X_1(Mp)$ at a place above $p$: the divisor $\sigma P - P$ produced by an inertia element acting on a point whose reduction is a crossing of the two components of the geometric special fibre is carried by an invertible module over the valuation ring which becomes trivial on each component. It is used in the construction of points of the Néron special fibre with vanishing image under the projection to the two components, in the orthogonality analysis of $J_1(Mp)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσI : σ ∈ Pl.inertiaSubgroupIn ℚ)
    (hσL : ∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l)
    (P P' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hP' : P'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
      Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ P.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))

    (Pt : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hPt : P.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ Pt.1)
    (uκ : Spec (CommRingCat.of k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (huκ' : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom πk) ≫ Pt.1) (huκ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (ν : ↥(pullback i₁.1 i₂.1)) (hν : uκ.base (IsLocalRing.closedPoint k) = (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base ν)

    (jη : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hjη₁ : jη ≫ pullback.fst _ _ = pullback.fst _ _)
    (hjη₂ : jη ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom Pl.subtype))
    (jk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hjk₁ : jk ≫ pullback.fst _ _ = pullback.fst _ _)
    (hjk₂ : jk ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk)) :
    ∃ M : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Modules, Scheme.Modules.IsInvertible M ∧
      Nonempty ((Scheme.Modules.pullback jη).obj M ≅
        (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (P'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
            (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, P'.2, Category.id_comp])).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (P.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
            (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, P.2, Category.id_comp])).idealModule) ∧
      Nonempty ((Scheme.Modules.pullback (i₁.1 ≫ jk)).obj M ≅ SheafOfModules.unit C₁.ringCatSheaf) ∧
      Nonempty ((Scheme.Modules.pullback (i₂.1 ≫ jk)).obj M ≅ SheafOfModules.unit C₂.ringCatSheaf) := by sorry
