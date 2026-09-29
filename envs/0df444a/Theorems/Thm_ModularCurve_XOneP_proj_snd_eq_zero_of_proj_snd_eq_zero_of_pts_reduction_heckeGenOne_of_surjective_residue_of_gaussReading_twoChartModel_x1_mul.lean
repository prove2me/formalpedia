-- Prove2me | Theorems.Thm_ModularCurve_XOneP_proj_snd_eq_zero_of_proj_snd_eq_zero_of_pts_reduction_heckeGenOne_of_surjective_residue_of_gaussReading_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.proj_snd_eq_zero_of_proj_snd_eq_zero_of_pts_reduction_heckeGenOne_of_surjective_residue_of_gaussReading_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/58e181f1-4d1a-575b-9fd5-e26a588c009c
-- title:
--   Triangularity of Uₚ on the Néron special fibre of J₁(Mp)
-- statement:
--   The statement is set in the following frame, whose hypotheses are grouped below; all hypotheses are named, and the content of the larger groups is summarised where indicated.
--
--   **Arithmetic data.** A prime $p$, a natural number $M$ with $M \neq 0$, $5 \le M$ (`hM`) and $p \nmid M$ (`hpM`); a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ for the set $\{p\}$, together with $\zeta \in L$ a primitive $p$-th root of unity (`hζ`); an intermediate field $K$ of $L \subseteq \mathrm{LaurentSeries}\,L$ with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103) (`hK`), i.e. $K$ is the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$; a discrete valuation domain $A$ with $L$ as fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ is in the image of $A$ (`hζA`), with $K$ an $A$-algebra compatibly with $A \subseteq L \subseteq K$; and $j \in K$ whose Laurent series is the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) (`hj`), with $j \neq 0$. Throughout, $X :=$ [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) denotes the structure morphism of the two-chart model over $\operatorname{Spec} A$ attached to these data, assumed proper.
--
--   **Special fibre and its two components.** An algebraically closed field $k$ of characteristic $p$ that is an $A$-algebra; schemes $C_1, C_2$ with morphisms $c_1, c_2$ to $\operatorname{Spec} k$ that are proper, smooth of relative dimension $1$ and geometrically integral; closed immersions $i_1 : C_1 \to X_k$, $i_2 : C_2 \to X_k$ over the base change $X_k$ of $X$ to $k$; `hcover`, asserting that every point of $X_k$ lies in the image of $i_1$ or of $i_2$; `hred`, that the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced; and a natural number $n$ with `Nat.card` of that intersection equal to $n$ (`hn`) and $0 < n$ (`hn0`).
--
--   **Sections.** A section $\varepsilon$ of $X$ over $\operatorname{Spec} A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$, and `hε₁`: $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   **Relative $\mathrm{Pic}^0$ data.** A designation $D$ for $X$ (a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section), with `hrep` asserting that $D$ represents, with rigidification along $\varepsilon$, the subfunctor of rigidified line bundles that are fibrewise algebraically equivalent to zero (`algEquivZeroCut`); `hsm` and `hsep`, that $D.\mathrm{toBase}$ is smooth and separated. Similarly `hreps` asserts that $D$ base changed to $k$ represents the corresponding functor for $X_k$ with the base-changed section, `hPk` identifies its Poincaré bundle with the base change of the Poincaré bundle over $A$, and $D_1, D_2$ with `hrep₁`, `hrep₂` are designations representing the analogous functors for $(c_1,\varepsilon_1)$ and $(c_2,\varepsilon_2)$.
--
--   **Restriction to the second component.** A morphism $\nu_2$ from $(D\text{ base changed to }k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ over $\operatorname{Spec} k$, with `hν₂` asserting that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of the base-changed designation, the line bundle obtained by pulling back the Poincaré bundle of `hrep₂` along $a$ followed by $\nu_2$ is isomorphic to the rigidification, along `rigSection c₂ t ε₂` and `pullback.snd c₂ t`, of the pullback along `curveChange i₂` of the line bundle obtained from the Poincaré bundle of `hreps` by pulling back along $a$; thus $\nu_2$ is the homomorphism induced by restriction of line bundles along $i_2$.
--
--   **Geometric generic fibre.** Compatible $A$- and $L$-algebra structures on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`; a curve model $M\eta$ over $\overline{\mathbb{Q}}$ for [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (an integral, proper, smooth relative dimension one scheme with an isomorphism of its function field with that field and a bijection of its closed points with the places); an isomorphism $e\eta$ from $M\eta.C$ to the fibre of $X$ over $\operatorname{Spec} \overline{\mathbb{Q}}$ compatible with the structure morphisms (`heη`); `Mη_chart_nonempty`, that the preimage under $e\eta$ followed by the first projection of the image of the finite chart [`ModularCurve.TwoChart.ιFin`](def/ModularCurve_TwoChartModel.html#L231) is nonempty; `hMηpin`, the $q$-expansion pin: for every $a$ in the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135), the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) obtained by transporting, through $M\eta.\mathrm{ffEquiv}^{-1}$, the germ at the generic point of the section determined by $a$ has Laurent series the image of the Laurent series of $a$ under [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) of $L \to \overline{\mathbb{Q}}$; and `hgal`, Galois equivariance: for every $\mathbb{Q}$-automorphism $g$ of $\overline{\mathbb{Q}}$ fixing the image of $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M\eta.C$, if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by the same composite for $x$, then $M\eta.\mathrm{pointEquivPlace}\,x' = \mathrm{arithmeticGalois}(g) \cdot M\eta.\mathrm{pointEquivPlace}\,x$.
--
--   **Group-theoretic model of the special fibre.** A datum $G$ of type [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), consisting of abelian groups $J0s$, $JI$, $JE$, a subgroup `torus` of $J0s$, and a surjective homomorphism $\mathrm{proj} : J0s \to JI \times JE$ with kernel `torus`. Bijections `pts`, `ptsI`, `ptsE` identify $J0s$, $JI$, $JE$ with the $k$-points of the base-changed designation, of $D_1$ and of $D_2$; `hadd`, `haddI`, `haddE` express additivity of these bijections as tensor-product isomorphisms of the corresponding pullbacks of the three Poincaré bundles; `hproj` asserts that for every $x \in J0s$ the point `ptsI (G.proj x).1` is `pts x` followed by the restriction morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and `ptsE (G.proj x).2` is `pts x` followed by $\nu_2$.
--
--   **Hecke data on the generic fibre.** A bijection `gpts` from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) (the degree-zero divisor class group of `x1FunctionFieldBar (M * p)`) to the $\overline{\mathbb{Q}}$-points of $D.\mathrm{toBase}$, additive for the relative group law coming from `hrep.some` (`hgadd`); a map $\varphi$ from [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) $= \mathrm{MvPolynomial}(\mathrm{Primes} \oplus \mathbb{N}, \mathbb{Z})$ to endomorphisms of $D.\mathrm{toBase}$ over $\operatorname{Spec} A$, each $\varphi(t)$ additive for the relative group law on $T$-points (`hφmul`), and `hφpts`: with respect to the module structure [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129), $(\mathrm{gpts}(t \cdot x)) = \mathrm{gpts}(x)$ followed by $\varphi(t)$ for all $t$ and all $x$.
--
--   **Abel–Jacobi data over $L$ and over $\overline{\mathbb{Q}}$** (the hypotheses `hDL`, `ajL`, `kL`, `ajbar`, `εbar`, `hPL`, `hajLε`, `hajL`, `hkL₁`, `hkL₂`, `hajbar`, `hajbar_over`, `hεbar`, `hεbar_aj`, `hpts_aj`, summarised here): `hDL` is representability after base change to $L$, `hPL` identifies the corresponding Poincaré bundle with the base change from $A$; `ajL` is a morphism from $X_L$ to the base-changed designation sending the section $\varepsilon_L$ to the zero section (`hajLε`) and satisfying the Abel–Jacobi property `hajL`, namely for every field $K'$, every morphism $t$ from $\operatorname{Spec} K'$ to $\operatorname{Spec} L$ and every $t$-point $x$ of $X_L$, the pullback of the Poincaré bundle along $x$ followed by `ajL` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of $t$ followed by $\varepsilon_L$; `kL` is a morphism from the $\overline{\mathbb{Q}}$-fibre to the $L$-fibre of $X$ compatible with both projections (`hkL₁`, `hkL₂`); `ajbar` is defined as $e\eta$ followed by `kL`, `ajL` and the first projection (`hajbar`), and lies over the base (`hajbar_over`); `εbar` is a $\overline{\mathbb{Q}}$-point of $M\eta.C$ inducing $\varepsilon$ (`hεbar`) and sent by `ajbar` to the zero section (`hεbar_aj`); and `hpts_aj` asserts that for all $\overline{\mathbb{Q}}$-points $x, s$ of $M\eta.C$ with $s$ inducing $\varepsilon$ there is a degree-zero divisor $D_v$ on `x1FunctionFieldBar (M * p)` equal to the difference of the single divisors at the places of $x$ and of $s$, whose class satisfies $\mathrm{gpts}(\mathrm{Pic}^0\text{-class of } D_v) = x$ followed by `ajbar`.
--
--   **The Igusa component.** An integral weight one form $w$ of level $M$ over $k$ (a weight one modular form for $\Gamma_1(M)$ with an integral $q$-expansion whose reduction is nonzero); a curve model $\mathrm{Mdl}_1$ over $k$ for the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), an isomorphism $e_1$ from $\mathrm{Mdl}_1.C$ to $C_1$ compatible with the structure morphisms (`he₁`), and `hne₁`, nonemptiness of the preimage of the finite chart; `hgauss₁`, the Gauss reading on $C_1$: for every $a$ in the finite chart algebra and all power series $x, y$ over $A$ with the reduction of $y$ to $k$ nonzero, if the Laurent series of $a$ times the image of $y$ in $L$ equals the image of $x$ in $L$, then the element of the Igusa function field obtained by transporting the germ of $a$ along $e_1$, $i_1$ and the first projection has Laurent series the quotient of the reduction of $x$ by the reduction of $y$. Further, an isomorphism of abelian groups $\theta_1$ from $JI$ to $\mathrm{Pic}^0$ of the Igusa function field with the pinning `hθpin₁`: for $g \in JI$ and a $k$-point $x$ of $c_1$, if the Poincaré pullback at `ptsI g` is isomorphic to the line bundle of the divisor of $x$ tensored with the ideal module of the divisor of $\varepsilon_1$, then there is a degree-zero divisor equal to the difference of the single divisors at the places of $x$ and of $\varepsilon_1$ (transported through $e_1^{-1}$) whose class is $\theta_1 g$; and a semilinear automorphism `frobIg` of the Igusa function field acting coefficientwise by $p$-th powers on Laurent coefficients (`hfrobIg`).
--
--   **The distinguished subgroup scheme.** A scheme $\mathcal{A}$ with a morphism $a$ to $\operatorname{Spec} A$ and a closed immersion $\iota$ of $\mathcal{A}$ into $D.P$ over $a$ (`h𝒜cl`), with $a$ proper (`h𝒜pr`) and smooth (`h𝒜sm`); `h𝒜conn`, that for every algebraically closed field and every morphism from its spectrum to $\operatorname{Spec} A$ the corresponding fibre of $a$ is connected; `h𝒜grp`, that for every $s : T \to \operatorname{Spec} A$ the $T$-points of $\mathcal{A}$ map under $\iota$ to a subgroup for the relative group law (a neutral element, closure under the group law, closure under inversion); `h𝒜gen`, that an element $x$ of [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) if and only if $\mathrm{gpts}(x)$ factors through $\iota$; and `h𝒜hecke`, that for every $t$ and every $T$-point $x$ of $\mathcal{A}$ the point obtained by applying $\varphi(t)$ to $\iota \circ x$ again factors through $\iota$.
--
--   **Place data.** A valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit in $Pl$ (`hPl`), a ring homomorphism $\rho : A \to Pl$ whose composite with the inclusion is the structure map $A \to \overline{\mathbb{Q}}$ (`hρ`), a subring $O \le Pl$ (`hO`) with a ring homomorphism $\rho_O : A \to O$ likewise compatible (`hρO`), and a ring homomorphism $\pi_k : Pl \to k$ with $\mathrm{algebraMap}\,A\,k = \pi_k \circ \rho$ (`hAlgk`) which is surjective (`hπk`).
--
--   **Conclusion.** For all $O$-points $z, z'$ of $D$ — that is, morphisms from $\operatorname{Spec} O$ to $D.P$ whose composite with $D.\mathrm{toBase}$ is $\operatorname{Spec}(\rho_O)$ — and all $y, y' \in G.J0s$, the following implication holds. Suppose
--
--   (i) the $k$-point `pts y` of the special fibre, composed with the first projection from the base-changed designation to $D.P$, equals the composite of $\operatorname{Spec}$ of $\pi_k \circ (\text{inclusion } O \subseteq Pl)$ with $z$; that is, $y$ is the reduction of $z$;
--
--   (ii) $z'$ is $z$ followed by $\varphi$ applied to [`ModularCurve.heckeGenOne ⟨p, _⟩`](def/ModularCurve_X1HeckeModule.html#L18), the generator of the Hecke algebra at the prime $p$;
--
--   (iii) the same reduction relation holds for $y'$ and $z'$, namely `pts y'` composed with the first projection equals $\operatorname{Spec}$ of $\pi_k \circ (\text{inclusion})$ followed by $z'$;
--
--   (iv) the second component $(G.\mathrm{proj}\,y).2 \in G.JE$ vanishes.
--
--   Then the second component $(G.\mathrm{proj}\,y').2$ vanishes as well.
--
--   This is the triangularity of the reduction of $U_p$ on the special fibre of the Néron model of $J_1(Mp)$ at $p$: the subgroup of $J^0_s$ on which the projection to the $\mathrm{Pic}^0$ of the étale component vanishes — the torus together with the part coming from the Igusa component — is stable under the endomorphism induced by the Hecke generator at $p$, so that the reduced $U_p$ on $J_I \times J_E$ has vanishing lower-left entry. It is stated for reductions of arbitrary $O$-points of $D$, with no condition imposed on the generic fibre, and is used both by the variant restricted to the norm-free part of $J_1(Mp)$ and by the construction of the Hecke action on the étale quotient of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_proj_snd_eq_zero_of_proj_snd_eq_zero_of_pts_reduction_heckeGenOne_of_surjective_residue_of_gaussReading_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
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
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.proj_snd_eq_zero_of_proj_snd_eq_zero_of_pts_reduction_heckeGenOne_of_surjective_residue_of_gaussReading_twoChartModel_x1_mul
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

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)

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

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)

    (h𝒜cl : IsClosedImmersion ι.1)

    (h𝒜pr : IsProper a) (h𝒜sm : Smooth a)
    (h𝒜conn : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s))

    (h𝒜grp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι)))

    (h𝒜gen : ∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1)

    (h𝒜hecke : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk) :

    ∀ (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase) (y y' : G.J0s),

      (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z.1 →

      z'.1 = z.1 ≫ (φ (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).1 →

      (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z'.1 →

      (G.proj y).2 = 0 →
      (G.proj y').2 = 0 := by sorry
