-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_points_smul_eq_and_reduction_eq_comp_galoisHom_of_points_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_points_smul_eq_and_reduction_eq_comp_galoisHom_of_points_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/dbc76126-0b28-5fea-8fa0-0ea22a73527f
-- title:
--   Galois transport of O-points of the Pic⁰ model
-- statement:
--   The setting is the two-chart integral model of $X_1(Mp)$ and a scheme $D.P$ representing its relative $\mathrm{Pic}^0$, together with the dictionaries relating $\overline{\mathbb{Q}}$-points, Hecke operators and Galois transport. The hypotheses are grouped as follows; every group is named, and the content of the longer groups is summarised.
--
--   *Arithmetic base.* A prime $p$, a natural number $M$ with $M \neq 0$, $5 \le M$ (`hM`) and $p \nmid M$ (`hpM`); a field $L$ of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, an element $\zeta \in L$ that is a primitive $p$-th root of unity (`hζ`); an intermediate field $K$ of $L((q))$ over $L$ with `hK` asserting $K =$ `laurentBaseChange L (x1FunctionField (M * p))`, the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the function field $X_1(Mp)$ over $\mathbb{Q}$; a discrete valuation domain $A$ with $L$ as fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ (`hζA`), together with an $A$-algebra structure on $K$ in a scalar tower over $L$; an element $j \in K$, nonzero, whose image in $L((q))$ is the $q$-expansion `coeffEmb L jq` of the modular invariant (`hj`). The relevant curve is [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), the morphism to $\operatorname{Spec} A$ obtained by gluing the spectra of the finite and infinite chart algebras, assumed proper.
--
--   *Special fibre.* An algebraically closed field $k$ of characteristic $p$ which is an $A$-algebra; two schemes $C_1, C_2$ with structure morphisms $c_1, c_2$ to $\operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral; closed immersions $i_1, i_2$ of $C_1, C_2$ into the base change of the model to $k$, over $c_1$, $c_2$ respectively; the covering hypothesis `hcover`, that every point of the fibre product lies in the image of $i_1$ or of $i_2$; `hred`, that `pullback i₁.1 i₂.1` is reduced; and a natural number $n$ with `hn` saying that this fibre product has exactly $n$ points and `hn0` saying $0 < n$.
--
--   *Sections.* A section $\varepsilon$ of the model over $\operatorname{Spec} A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ over $\operatorname{Spec} k$, and `hε₁`, that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   *Representability of $\mathrm{Pic}^0$.* A designation $D$ (a scheme $D.P$ with structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section), with `hrep` a witness that $D$ represents the functor of rigidified line bundles satisfying the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`, and `hsm`, `hsep` asserting that $D.\mathrm{toBase}$ is smooth and separated; `hreps`, the corresponding representability of `D.baseChange k` for the curve over $k$ with the base-changed section, and `hPk`, an isomorphism of its Poincaré bundle with the base change to $k$ of the pullback of the Poincaré bundle of `hrep.some` along the first projection; designations $D_1, D_2$ for $c_1, c_2$ with representability witnesses `hrep₁`, `hrep₂`; a morphism $\nu_2$ from $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ over $\operatorname{Spec} k$ together with `hν₂`, which for every $k$-scheme $T$ and every point $a$ of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$ over $T$ identifies the pullback of the Poincaré bundle of `hrep₂.some` along $a$ followed by $\nu_2$ with the rigidification along `rigSection c₂ t ε₂` of the pullback along `curveChange i₂.1` of the bundle obtained from `hreps.poincare` by pulling back along $a$.
--
--   *Geometric generic fibre.* Algebra structures of $A$ and $L$ on $\overline{\mathbb{Q}}$ forming a scalar tower; `hsmL`, `hgiL`, that the base change of the model to $L$ is smooth of relative dimension $1$ and geometrically integral; `hprL`, `hgcL`, that `pullback.snd D.toBase (specMap A L)` is proper and geometrically connected; a curve model $M\eta$ over $\overline{\mathbb{Q}}$ with function field `x1FunctionFieldBar (M * p)`, an isomorphism $e\eta$ from $M\eta.C$ to the base change of the model to $\overline{\mathbb{Q}}$ with `heη` saying that $e\eta$ followed by the second projection is $M\eta.\mathrm{toBase}$; the nonemptiness of the open subscheme of $M\eta.C$ obtained as the preimage, under $e\eta$ followed by the first projection, of the image of the finite chart; the pinning `hMηpin`, which for each element $a$ of the finite chart algebra identifies, via $M\eta.\mathrm{ffEquiv}^{-1}$ and the germ at the generic point, the corresponding function-field element with the coefficientwise image along $L \to \overline{\mathbb{Q}}$ of the Laurent series of $a$; and `hgal`, which for every $g \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing the image of $L$ pointwise and every two $\overline{\mathbb{Q}}$-points $x, x'$ of $M\eta.C$ such that $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec} g$ followed by the same composite for $x$, asserts $M\eta.\mathrm{pointEquivPlace}\,x' = \mathrm{arithmeticGalois}(x_1\mathrm{FunctionField}(Mp))(g) \cdot M\eta.\mathrm{pointEquivPlace}\,x$.
--
--   *Hecke and diamond inputs.* `hin` and `hcomm`, the predicates `HeckeDiamondInputsAll (M * p)` and `HeckeDiamondCommuteBar (M * p)` (the latter the commutation of the barred diamond/Hecke generators, the former the collection of Hecke inputs along primes and the existence of diamond automorphisms and their base changes).
--
--   *Galois action on $A$.* A multiplicative semiring action of $\mathrm{Gal}(L/\mathbb{Q})$ on $A$ with `hΓA` saying that it is compatible, via $A \to L$, with the action on $L$.
--
--   *Special-fibre group data.* An object $G$ of type [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), i.e. abelian groups $G.J_{0s}$, $G.J_I$, $G.J_E$, a subgroup `torus` of $G.J_{0s}$ and a surjection $\mathrm{proj} : G.J_{0s} \to G.J_I \times G.J_E$ with kernel `torus`; bijections `pts`, `ptsI`, `ptsE` of these three groups with the $k$-points of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$; the additivity hypotheses `hadd`, `haddI`, `haddE`, each asserting that the pullback of the relevant Poincaré bundle at a sum of points is isomorphic to the tensor product of the pullbacks; and `hproj`, which for every $x$ identifies `ptsI (G.proj x).1` with `pts x` followed by the pullback morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$ and `hε₁`, and `ptsE (G.proj x).2` with `pts x` followed by $\nu_2$.
--
--   *Generic dictionary, Hecke operators and transport.* A bijection `gpts` between $\mathrm{Pic}^0$ of `x1FunctionFieldBar (M * p)` and the $\overline{\mathbb{Q}}$-points of $D.\mathrm{toBase}$; a map $\varphi$ from `HeckeAlgOne` to endomorphisms of $D.\mathrm{toBase}$ over $\operatorname{Spec} A$; for each $s \in \mathrm{Gal}(L/\mathbb{Q})$ a morphism $\tau(s)$ of $D.P$ lying over $\operatorname{Spec}$ of the ring automorphism of $A$ given by $s$; `hφmul`, that each $\varphi(t)$ is additive for the relative group law supplied by `hrep.some`; `hφpts`, that for the Hecke module structure `heckeModuleOneBar` one has $\mathrm{gpts}(t \cdot x) = \mathrm{gpts}(x)$ followed by $\varphi(t)$; `hτ1`, `hτmul`, that $\tau(1)$ is the identity of $D.P$ and $\tau(ss')$ is $\tau(s)$ followed by $\tau(s')$; `hτφ`, that $\tau(s)$ and $\varphi(t)$ commute; `hgadd`, that `gpts` is additive for that relative group law; and `hτpts`, that whenever $\sigma' \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ restricts on $L$ to $s$, then $\mathrm{gpts}(\sigma' \cdot x) = \operatorname{Spec}\sigma'$ followed by $\mathrm{gpts}(x)$ followed by $\tau(s^{-1})$.
--
--   *Abel–Jacobi data over $L$ and over $\overline{\mathbb{Q}}$.* A representability witness `hDL` for the base change of the model to $L$; a morphism `ajL` from that base change to $(D.\mathrm{baseChange}\,L).\mathrm{toBase}$ over the curve; a morphism `kL` from the fibre product over $\overline{\mathbb{Q}}$ to the one over $L$; a morphism `ajbar` from $M\eta.C$ to $D.P$; a $\overline{\mathbb{Q}}$-point `εbar` of $M\eta.C$; `hPL`, the analogue of `hPk` over $L$; `hajLε`, that the base-changed section followed by `ajL` is the zero section; `hajL`, the Abel–Jacobi property, namely that for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every point $x$ of the curve over $t$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by `ajL` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor cut out by the section; `hkL₁`, `hkL₂`, the compatibilities of `kL` with the two projections; `hajbar`, defining `ajbar` as $e\eta$ followed by `kL`, `ajL` and the first projection; `hajbar_over`, that `ajbar` lies over $M\eta.\mathrm{toBase}$ followed by `specMap A (AlgebraicClosure ℚ)`; `hεbar` and `hεbar_aj`, that `εbar` lies over $\varepsilon$ and is carried by `ajbar` to the zero section; and `hpts_aj`, that for all $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M\eta.C$ with $s$ lying over $\varepsilon$ there is a degree-zero divisor $D_v$ on `x1FunctionFieldBar (M * p)` equal to the difference of the places of $x$ and of $s$, such that $\mathrm{gpts}$ of its class in $\mathrm{Pic}^0$ is $x$ followed by `ajbar`.
--
--   *Local data at $p$ and the automorphism.* A valuation subring $P\ell$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits (`hPl`); a ring homomorphism $\rho : A \to P\ell$ with $\rho$ followed by the inclusion equal to $A \to \overline{\mathbb{Q}}$ (`hρ`); a subring $O$ of $\overline{\mathbb{Q}}$ contained in $P\ell$ (`hO`) and a ring homomorphism $\rho_O : A \to O$ with the analogous compatibility (`hρO`); a ring homomorphism $\pi_k : P\ell \to k$ with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`); finally $\sigma' \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $s \in \mathrm{Gal}(L/\mathbb{Q})$ with $\sigma'$ restricting to $s$ on the image of $L$ (`hs`), with $\sigma'(O) \subseteq O$ (`hσO`) and $\sigma'(P\ell) \subseteq P\ell$ (`hσPl`), and a ring homomorphism $\bar\sigma : k \to k$ with $\pi_k(\sigma' x) = \bar\sigma(\pi_k x)$ for all $x \in P\ell$ (`hσbar`).
--
--   Under these hypotheses the conclusion is the following. For every $x$ in $\mathrm{Pic}^0$ of `x1FunctionFieldBar (M * p)` and every morphism $z : \operatorname{Spec} O \to D.P$ lying over $\operatorname{Spec} \rho_O$, such that the $\overline{\mathbb{Q}}$-point $\mathrm{gpts}(x)$ equals $\operatorname{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ followed by $z$, there exists a morphism $z' : \operatorname{Spec} O \to D.P$ lying over $\operatorname{Spec}\rho_O$ such that:
--
--   first, the $\overline{\mathbb{Q}}$-point $\mathrm{gpts}(\sigma' \cdot x)$ equals $\operatorname{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ followed by $z'$;
--
--   second, $\operatorname{Spec}$ of $\pi_k$ composed with the inclusion of $O$ into $P\ell$, followed by $z'$, equals $\operatorname{Spec}\bar\sigma$ followed by ($\operatorname{Spec}$ of that same homomorphism followed by $z$) and then by $\tau(s^{-1})$.
--
--   Thus the $O$-integral point of $D.P$ representing $x$ can be transported to one representing $\sigma' \cdot x$, and its reduction to $k$ is the $\bar\sigma$-twist of the reduction of $z$ composed with the transport morphism $\tau(s^{-1})$.
--
--   This is the transport-of-structure step that carries the Galois action on $\mathrm{Pic}^0$ of $X_1(Mp)$ over $\overline{\mathbb{Q}}$ to integral points of the $\mathrm{Pic}^0$ model over a valuation subring above $p$ and records the effect on their reductions into the special fibre. It is used in the analysis of the special fibre of $J_1(Mp)$ at $p$, where taking $\sigma'$ in the inertia subgroup makes $\bar\sigma$ the identity; the statements about the norm-free part family, its Hecke equivariance, its behaviour under the decomposition subgroup and its pairing cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_points_smul_eq_and_reduction_eq_comp_galoisHom_of_points_twoChartModel_x1_mul.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_points_smul_eq_and_reduction_eq_comp_galoisHom_of_points_twoChartModel_x1_mul
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

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

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
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

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

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

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
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L)
    (hs : ∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l))
    (hσO : ∀ x : AlgebraicClosure ℚ, x ∈ O → σ' x ∈ O)
    (hσPl : ∀ x : AlgebraicClosure ℚ, x ∈ Pl → σ' x ∈ Pl)
    (σbar : k →+* k)
    (hσbar : ∀ x : ↥Pl, πk ⟨σ' x, hσPl x x.2⟩ = σbar (πk x)) :
    ∀ (x : ModularCurve.JOne (M * p)) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase),
      (gpts x).1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ z.1 →
      ∃ z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase,
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ z'.1 ∧
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z'.1 =
          Spec.map (CommRingCat.ofHom σbar) ≫
            (Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z.1) ≫ (τ s⁻¹).1 := by sorry
