-- Prove2me | Theorems.Thm_ModularCurve_XOneP_smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/c4b1cf57-1ddd-56e6-adba-80c5b089a04a
-- title:
--   Prime-to-p torsion with a Pl-integral point is inertia-fixed
-- statement:
--   Throughout, $p$ is a prime and $M$ a natural number with $5 \le M$ and $p \nmid M$.
--
--   **Base arithmetic data.** $L$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for the set $\{p\}$, and $\zeta \in L$ is a primitive $p$-th root of unity. $K$ is an intermediate field of the Laurent series field $L((q))$ over $L$, subject to `hK`: $K$ equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$. $A$ is a discrete valuation domain with an $A$-algebra structure on $L$ making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ in $L$ (`hζA`); $K$ is an $A$-algebra compatibly with the tower $A \to L \to K$. Finally $j$ is a nonzero element of $K$ whose Laurent expansion is the coefficientwise image in $L((q))$ of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function (`hj`). The associated two-chart $A$-model is the structural morphism [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252), glued from the spectra of the finite chart subalgebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135) and of the chart at infinity; it is assumed proper.
--
--   **The special fibre and its two components.** $k$ is an algebraically closed field of characteristic $p$ and an $A$-algebra. $C_1, C_2$ are schemes with morphisms $c_1, c_2$ to $\operatorname{Spec} k$ that are proper, smooth of relative dimension $1$ and geometrically integral. Writing $X_k$ for the base change `pullback (ModularCurve.TwoChart.modelTo A ↥K j) (specMap A k)`, the data $i_1, i_2$ are morphisms $C_1 \to X_k$, $C_2 \to X_k$ over $k$ (i.e. elements of `SchemeHomOver c₁ (baseChange A … k)` and `SchemeHomOver c₂ (baseChange A … k)`), both closed immersions. The hypothesis `hcover` requires that every point of $X_k$ lie in the image of $i_1$ or of $i_2$; `hred` requires the scheme `pullback i₁.1 i₂.1` to be reduced, and `hn`, `hn0` name its cardinality $n$ and require $0 < n$.
--
--   **Sections.** $\varepsilon$ is a section of [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec} A$, and $\varepsilon_1, \varepsilon_2$ are sections of $c_1, c_2$ over $\operatorname{Spec} k$; `hε₁` requires $\varepsilon_1$ followed by $i_1$ to be the base-changed section `sectionBaseChange k ε`.
--
--   **Relative Picard data.** $D$ is a `RelativePic0Designation A (ModularCurve.TwoChart.modelTo A ↥K j)`, that is, a scheme $P$ with a morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section of it. The hypothesis `hrep` requires that $D$ represent, in the sense of `RepresentsRelSubPic`, the functor of $\varepsilon$-rigidified line bundles on the two-chart model satisfying the fibrewise algebraically-trivial condition `algEquivZeroCut`: there is a Poincaré rigidified bundle on the pullback over `D.toBase` satisfying that condition, every such rigidified bundle over a base $t$ is the pullback of the Poincaré bundle along a unique morphism over $\operatorname{Spec} A$, and the restriction along the zero section is trivial. Further, `hsm` and `hsep` require `D.toBase` to be smooth and separated; `hreps` is a chosen witness that `D.baseChange k` represents the corresponding functor for $X_k$ with the base-changed section; `hPk` requires the Poincaré bundle of `hreps` to be isomorphic to the base change to $k$ (via `BaseChange.ofR`) of the pullback of the Poincaré bundle of `hrep.some` along `pullback.fst D.toBase (specMap A k)`. Likewise $D_1$, $D_2$ are relative $\operatorname{Pic}^0$ designations over $k$ for $c_1, c_2$, with witnesses `hrep₁`, `hrep₂` of representability relative to $\varepsilon_1, \varepsilon_2$.
--
--   $\nu_2$ is a morphism from `(D.baseChange k).toBase` to `D₂.toBase` over $\operatorname{Spec} k$, pinned by `hν₂`: for every scheme $T$ over $k$ with structure morphism $t$ and every point $a$ of `(D.baseChange k).toBase` over $t$, the pullback of the Poincaré bundle of `hrep₂.some` along the composite of $a$ with $\nu_2$ is isomorphic to the rigidification `Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)` of the pullback along `curveChange i₂.1 i₂.2 t` of the bundle obtained from `hreps.poincare` by pulling back along $a$; thus $\nu_2$ is the map on relative Picard schemes induced by the closed immersion $i_2$.
--
--   **Geometric generic fibre and the Galois dictionary.** $M_\eta$ is a `CurveModel` over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` of the field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) — an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec} \overline{\mathbb{Q}}$, with a ring isomorphism onto its function field compatible with the base, and a bijection between its closed points and the places of that field satisfying the stalk and affine-cover conditions — together with an isomorphism $e_\eta$ from `Mη.C` to `pullback (ModularCurve.TwoChart.modelTo A ↥K j) (specMap A (AlgebraicClosure ℚ))` compatible with the morphisms to $\operatorname{Spec}\overline{\mathbb{Q}}$ (`heη`); here $\overline{\mathbb{Q}}$ is an $A$- and $L$-algebra compatibly with the tower. The instance `Mη_chart_nonempty` requires the open subscheme of `Mη.C` obtained by pulling back the open image of the finite chart [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231) along $e_\eta$ followed by the first projection to be nonempty, and `hMηpin` requires, for every $a$ in the finite chart algebra, that the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) corresponding under `Mη.ffEquiv.symm` to the germ of (the section determined by) $a$ on that open have Laurent expansion equal to the image under [`ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ))`](def/ModularCurve_LaurentCoeff.html#L16) of the Laurent expansion of $a$ viewed in $K$. The hypothesis `hgal` requires, for every $g \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing the image of $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of `Mη.C`, that if $x'$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by $x$, $e_\eta$ and the first projection, then `Mη.pointEquivPlace x'` is the translate of `Mη.pointEquivPlace x` under the semilinear automorphism [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Group-theoretic data on the special fibre.** $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s` and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. The bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the sections over $\operatorname{Spec} k$ of `(D.baseChange k).toBase`, `D₁.toBase`, `D₂.toBase` respectively; `hadd`, `haddI`, `haddE` require each of these identifications to be additive, in the sense that the Poincaré bundle pulled back along the point attached to a sum is isomorphic to the tensor product of the pullbacks along the points attached to the summands; and `hproj` requires, for every $x \in$ `G.J0s`, that `ptsI (G.proj x).1` be `pts x` followed by the morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some` induced by $i_1$, and that `ptsE (G.proj x).2` be `pts x` followed by $\nu_2$.
--
--   **Igusa identification of the components.** $w$ is a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16): a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion whose reduction over $k$ is nonzero. $\mathrm{Mdl}_1$ and $\mathrm{Mdl}_2$ are curve models over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), with isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$ and $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`).
--
--   **Abel–Jacobi dictionary.** `gpts` is a bijection between [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group $\operatorname{Pic}^0$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$, and the $\overline{\mathbb{Q}}$-points of `D.toBase` over $\operatorname{Spec} A$, and `hgadd` requires it to be additive for the relative group law on `D.toBase` supplied by `hrep.some`. The remaining block pins this dictionary down over $L$ and over $\overline{\mathbb{Q}}$: `hDL` is a witness that `D.baseChange L` represents the relative Picard functor of the base change of the model to $L$ with the base-changed section; `ajL` is a morphism from that base change to `(D.baseChange L).toBase` over $\operatorname{Spec} L$; `kL` is a morphism from the $\overline{\mathbb{Q}}$-fibre of the model to its $L$-fibre, with `hkL₁`, `hkL₂` expressing compatibility with the two projections (the second up to `specMap L (AlgebraicClosure ℚ)`); `ajbar` is a morphism `Mη.C ⟶ D.P` and `εbar` a $\overline{\mathbb{Q}}$-point of `Mη.C`. The hypothesis `hPL` requires the Poincaré bundle of `hDL` to be isomorphic to the base change to $L$ of the pullback of `hrep.some.poincare` along `pullback.fst D.toBase (specMap A L)`; `hajLε` requires the composite of the base-changed section with `ajL` to be the zero section of `D.baseChange L`; `hajL` requires, for every field $K'$, every morphism $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every point $x$ of the $L$-fibre over $t$, that the pullback of the Poincaré bundle of `hDL` along $x$ followed by `ajL` be isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to $x$ with the ideal module of the divisor attached to the point $t$ followed by the base-changed section — that is, `ajL` is the Abel–Jacobi map $x \mapsto [x - \varepsilon]$. The hypotheses `hajbar`, `hajbar_over` require `ajbar` to be the composite of $e_\eta$, `kL`, `ajL` and `pullback.fst D.toBase (specMap A L)`, and to lie over `Mη.toBase` followed by `specMap A (AlgebraicClosure ℚ)`; `hεbar` and `hεbar_aj` require `εbar` to be the $\overline{\mathbb{Q}}$-point coming from the section $\varepsilon$ and to be sent by `ajbar` to the zero section. Finally `hpts_aj` requires that for all $\overline{\mathbb{Q}}$-points $x, s$ of `Mη.C` with $s$ the point coming from $\varepsilon$, there exist a degree-zero divisor $Dv$ on [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) whose underlying divisor is $[\,$place of $x\,] - [\,$place of $s\,]$ (in terms of `Mη.pointEquivPlace`) and such that the point `gpts (Pic0.mk Dv)` is $x$ followed by `ajbar`.
--
--   **The place above $p$ in $\overline{\mathbb{Q}}$.** $\mathrm{Pl}$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hPl` requiring $p$ to be a non-unit of $\mathrm{Pl}$; $\rho : A \to \mathrm{Pl}$ is a ring homomorphism factoring the structure map $A \to \overline{\mathbb{Q}}$ (`hρ`); and $\pi_k : \mathrm{Pl} \to k$ is a surjective ring homomorphism with $\rho$ followed by $\pi_k$ equal to the structure map $A \to k$ (`hAlgk`, `hπk`).
--
--   **Conclusion.** For every $\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in `Pl.inertiaSubgroupIn ℚ`, the image in the decomposition group of the inertia subgroup of $\mathrm{Pl}$, such that $\sigma$ fixes $\operatorname{algebraMap} L\, \overline{\mathbb{Q}}\,(l)$ for every $l \in L$; for every natural number $m$ with $0 < m$ and $p \nmid m$; for every $x \in$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) with $m \cdot x = 0$; and for every point $z$ of `D.toBase` over $\operatorname{Spec}(\rho)$, that is, every $\mathrm{Pl}$-point of $D$ over $A$, such that the $\overline{\mathbb{Q}}$-point `gpts x` is $\operatorname{Spec}$ of the inclusion $\mathrm{Pl} \hookrightarrow \overline{\mathbb{Q}}$ followed by $z$ — one has $\sigma \cdot x = x$.
--
--   This is the 'finite part is inertia-fixed' half of the specialisation analysis of $J_1(Mp)$ at a place above $p$ over $\mathbb{Q}(\zeta_p)$: for $m$ prime to $p$ the $m$-torsion of the smooth separated relative $\operatorname{Pic}^0$ is étale over the base, so a torsion class whose Abel–Jacobi point extends to the valuation ring $\mathrm{Pl}$ is determined by its reduction, on which inertia acts trivially. It feeds the two companion results in the same block on prime-to-$p$ classes with vanishing projection and on the associated Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
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
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ ∈ Pl.inertiaSubgroupIn ℚ →
      (∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (m : ℕ), 0 < m → ¬ p ∣ m →
        ∀ (x : ModularCurve.JOne (M * p)), m • x = 0 →
          ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
            (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 →
              σ • x = x := by sorry
