-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/4df7fc8a-7601-56bc-991d-59962b1f734c
-- title:
--   Level-p Hecke divisor of a Gauss-reducing place of X₁(Mp)
-- statement:
--   Arithmetic setting. Fixed are a prime $p$, an integer $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, a primitive $p$-th root of unity $\zeta \in L$, and an intermediate field $K$ of $L((q))$ over $L$ equal (hypothesis `hK`) to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the $q$-expansion field of $X_1(Mp)$ over $\mathbb{Q}$. Further, $A$ is a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal (`hAp`) and $\zeta$ is in the image of $A$ (`hζA`), $K$ is an $A$-algebra compatibly with $L$, and $j \in K$ is a nonzero element whose Laurent series is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`). The scheme over $\operatorname{Spec} A$ throughout is the two-chart model [`ModularCurve.TwoChart.modelTo A (↥K) j`](def/ModularCurve_TwoChartModel.html#L252), the pushout of the spectra of the two subalgebras `chartAlgFin` and `chartAlgInf` of elements of $K$ integral over $A[j]$, respectively $A[j^{-1}]$, with [`ModularCurve.TwoChart.ιFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L231) the chart morphism out of the spectrum of `chartAlgFin A (↥K) j`; the model is assumed proper over $\operatorname{Spec} A$.
--
--   Special fibre. $k$ is an algebraically closed $A$-algebra field of characteristic $p$. Two proper smooth geometrically integral $k$-curves $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ of relative dimension $1$ are given together with closed immersions $i_1, i_2$ into the base change of the model to $k$, over $k$. The hypotheses on the special fibre are: `hcover`, every point of the base change to $k$ lies in the image of $i_1$ or of $i_2$; `hred`, the fibre product `pullback i₁.1 i₂.1` is reduced; `hn` and `hn0`, its number of points is $n$ with $0 < n$. Sections are fixed: $\varepsilon$ of the model over $\operatorname{Spec} A$, and $\varepsilon_1$, $\varepsilon_2$ of $c_1$, $c_2$, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   Relative Picard data. $D$ is a `RelativePic0Designation` for the model over $A$ (a scheme with a structure morphism to $\operatorname{Spec} A$ and a zero section), and `hrep` states that $D$ represents the relative subfunctor of rigidified invertible modules satisfying the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`, in the sense of `RepresentsRelSubPic` (a Poincaré rigidified line bundle in the class, a universal property classifying such bundles up to isomorphism, and triviality along the zero section); `hsm` and `hsep` assert that $D$'s structure morphism is smooth and separated. The further representability hypotheses are `hreps` for the base change of $D$ to $k$ with the base-changed section, together with `hPk` identifying its Poincaré bundle with the base change along `BaseChange.ofR` of the pullback of the Poincaré bundle of $D$, and `hrep₁`, `hrep₂` for designations $D_1$, $D_2$ over $k$ attached to $c_1$, $c_2$ with their sections. The morphism $\nu_2$ goes from the base change of $D$ to $k$ to $D_2$ over $k$, and `hν₂` asserts that for every $k$-scheme $T$ and every $T$-point $a$ of the base change of $D$, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification along the section of $c_2$ of the pullback, along `curveChange i₂`, of the bundle classified by $a$; thus $\nu_2$ induces pullback of line bundles along $i_2$.
--
--   Geometric generic fibre. Algebra structures $A \to \overline{\mathbb{Q}}$ and $L \to \overline{\mathbb{Q}}$ with the scalar tower are fixed, $\overline{\mathbb{Q}}$ denoting `AlgebraicClosure ℚ`. $M_\eta$ is a `CurveModel` over $\overline{\mathbb{Q}}$ of the geometric function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper smooth integral curve with a ring isomorphism onto its function field, compatibly with the base field, and a bijection `pointEquivPlace` between its $\overline{\mathbb{Q}}$-points and the places of the field), $e_\eta$ is an isomorphism of $M_\eta.C$ with the base change of the model to $\overline{\mathbb{Q}}$, and `heη` says $e_\eta$ followed by the second projection is the structure morphism of $M_\eta$. The chart hypotheses are `Mη_chart_nonempty`, the preimage in $M_\eta.C$ of the finite chart is nonempty, and `hMηpin`, the $q$-expansion pin: for every $a$ in `chartAlgFin A (↥K) j`, the element of the function field obtained from $a$ by transporting it through the chart along $e_\eta$ followed by the first projection and taking the germ at the generic point has, as a Laurent series over $\overline{\mathbb{Q}}$, the coefficientwise image of the Laurent series of $a$ over $L$. The hypothesis `hgal` is Galois equivariance: for every $\mathbb{Q}$-automorphism $g$ of $\overline{\mathbb{Q}}$ fixing $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$, if $x'$ composed into the model equals $x$ composed into the model precomposed with $\operatorname{Spec}$ of $g$, then `Mη.pointEquivPlace x'` is the image of `Mη.pointEquivPlace x` under the semilinear automorphism [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54) acting on places.
--
--   Néron special-fibre group and Hecke action. $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `J0s`, `JI`, `JE`, a subgroup `torus` of `J0s`, and a surjective homomorphism $\mathrm{proj} : \mathrm{J0s} \to \mathrm{JI} \times \mathrm{JE}$ with kernel `torus`. Bijections `pts`, `ptsI`, `ptsE` identify `J0s`, `JI`, `JE` with the $k$-points of the base change of $D$, of $D_1$ and of $D_2$; `hadd`, `haddI`, `haddE` assert that under each of these the group law corresponds to the tensor product of the classified Poincaré pullbacks; `hproj` asserts that for every $x$ the first component of $\mathrm{proj}(x)$ corresponds to $x$ postcomposed with the morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$, and the second component to $x$ postcomposed with $\nu_2$. On the generic side, `gpts` identifies [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group of `x1FunctionFieldBar (M * p)`, with the $\overline{\mathbb{Q}}$-points of $D$ over $\operatorname{Spec} A$, additively for the relative group law coming from `hrep` (`hgadd`). The map $\varphi$ assigns to each element of the Hecke algebra [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) an endomorphism of $D$ over $\operatorname{Spec} A$, with `hφmul` stating that each $\varphi(t)$ respects the relative group law on points over any base, and `hφpts` stating that for the Hecke module structure [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129) on `JOne (M * p)` one has $\mathrm{gpts}(t \cdot x) = \mathrm{gpts}(x)$ followed by $\varphi(t)$.
--
--   Abel–Jacobi data. The group `hDL` asserts representability of the relative subfunctor for the base change of the model and of $D$ to $L$; $ajL$ is a morphism from the base-changed curve to the base change of $D$ over $L$, with `hajLε` sending the section to the zero section, and `hajL` the Abel–Jacobi property: for every field $K'$, every $L$-point $t$ of $\operatorname{Spec} K'$ and every $T$-point $x$ of the curve, the Poincaré pullback along $x$ followed by $ajL$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the section; $kL$ is a comparison morphism between the geometric fibres over $\overline{\mathbb{Q}}$ and over $L$ with `hkL₁`, `hkL₂` its two projection compatibilities, and `hPL` identifies the Poincaré bundle over $L$ with the base change of that of $D$. The morphism $\overline{aj}$ is defined by `hajbar` as $e_\eta$ followed by $kL$, $ajL$ and the first projection, lies over the base by `hajbar_over`, and $\overline{\varepsilon}$ is a $\overline{\mathbb{Q}}$-point of $M_\eta.C$ which maps to $\varepsilon$ (`hεbar`) and is sent by $\overline{aj}$ to the zero section (`hεbar_aj`). Finally `hpts_aj` asserts that for all $\overline{\mathbb{Q}}$-points $x$, $s$ of $M_\eta.C$ with $s$ the $\varepsilon$-point, there is a degree-zero divisor $D_v$ equal to $[\,\mathrm{place}(x)\,] - [\,\mathrm{place}(s)\,]$ whose class under `gpts` is $x$ followed by $\overline{aj}$.
--
--   Igusa component. $w$ is an `IntegralWeightOneForm k M`: a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion, whose image in $k((q))$ is nonzero; [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) is the field obtained from the $X_1(M)$ function field over $k$ by adjoining the inverse of that series. $\mathrm{Mdl}_1$ is a curve model of this field over $k$, $e_1 : \mathrm{Mdl}_1.C \cong C_1$ an isomorphism over $k$ (`he₁`). The hypotheses `hne₁` (nonemptiness of the corresponding chart preimage in $\mathrm{Mdl}_1.C$) and `hgauss₁` (the Gauss pin) govern the identification: `hgauss₁` states that for $a$ in `chartAlgFin A (↥K) j` and power series $x, y$ over $A$ with $\bar y \neq 0$ in $k[[q]]$, if $a \cdot y = x$ as Laurent series over $L$, then the element of the Igusa field attached to $a$ through the chart along $e_1$ followed by $i_1$ and the first projection has Laurent series $\bar x / \bar y$ over $k$. Further, $\theta_1$ is an isomorphism of `G.JI` with the degree-zero class group of the Igusa field, and `hθpin₁` states that if the Poincaré pullback at $\mathrm{ptsI}(g)$ is isomorphic to the line bundle of a $k$-point $x$ of $c_1$ tensored with the ideal module of $\varepsilon_1$, then $\theta_1(g)$ is the class of $[\,\mathrm{place}(x)\,] - [\,\mathrm{place}(\varepsilon_1)\,]$ on $\mathrm{Mdl}_1$. The element $\mathrm{frobIg}$ is a semilinear automorphism of the Igusa field over $k$ (a pair of compatible ring automorphisms of the field and of $k$) acting on each Laurent coefficient by $x \mapsto x^p$ (`hfrobIg`).
--
--   Reduction data. $\mathrm{Pl}$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of it (`hPl`), $\rho : A \to \mathrm{Pl}$ and $\rho_O : A \to O$ are ring homomorphisms compatible with the structure maps to $\overline{\mathbb{Q}}$ (`hρ`, `hρO`) for a subring $O \le \mathrm{Pl}$ (`hO`), and $\pi_k : \mathrm{Pl} \to k$ satisfies $\mathrm{algebraMap}_{A,k} = \pi_k \circ \rho$ (`hAlgk`) and is surjective (`hπk`); the hypothesis `hOPl` gives the reverse inclusion $\mathrm{Pl} \le O$. The map $\mathrm{red}_1$ sends places of `x1FunctionFieldBar (M * p)` to places of the Igusa field, and `hred₁` characterises it where defined geometrically: for a place $P$, an $O$-point $\xi$ of the model over $\operatorname{Spec}$ of $\rho_O$, and a $k$-point $c$ of $c_1$, if $\xi$ restricted along $O \hookrightarrow \overline{\mathbb{Q}}$ is the point of the model attached to $P$ through `Mη.pointEquivPlace.symm` and $e_\eta$, and if $c$ followed by $i_1$ and the first projection is $\xi$ composed with $\operatorname{Spec}$ of $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$, then $\mathrm{red}_1(P)$ is the place of the Igusa field attached to $c$ transported by $e_1^{-1}$.
--
--   Hecke correspondence inputs. `hβdef` is [`ModularCurve.HeckeBetaOneDefined (M * p) p`](def/ModularCurve_X1HeckeOperator.html#L84), i.e. $q \mapsto q^p$ carries the $X_1(Mp)$ field into the field of $X_1(Mp) \cap X_0(Mp\cdot p)$; `hα` and `hβ` assert integrality of the two $\overline{\mathbb{Q}}$-algebra maps `heckeAlphaOneBar` (the inclusion) and `heckeBetaOneBar`; a principal-divisor instance is assumed for the base change of the $X_1/X_0$ field; and `hdeg` states that the degree `finrankAlong` of `heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p` equals $p$.
--
--   Conclusion. For every place $P$ of `x1FunctionFieldBar (M * p)` satisfying the Gauss-reduction condition — there exist an $O$-point $\xi$ of the model over $\operatorname{Spec}$ of $\rho_O$ and a $k$-point $c$ of $c_1$ such that ($\mathrm{i}$) $\xi$ restricted along $O \hookrightarrow \overline{\mathbb{Q}}$ equals the point attached to $P$ composed with $e_\eta$ and the first projection, ($\mathrm{ii}$) $c$ followed by $i_1$ and the first projection equals $\xi$ precomposed with $\operatorname{Spec}$ of $\pi_k \circ (O \hookrightarrow \mathrm{Pl})$, ($\mathrm{iii}$) no point of the source of $c$ has image in the range of the first projection of `pullback i₁.1 i₂.1`, and ($\mathrm{iv}$) every point of the source maps, under $c$ followed by $i_1$ and the first projection, into the range of [`ModularCurve.TwoChart.ιFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L231) — there exists a family $Q : \mathrm{Fin}\,p \to$ places of `x1FunctionFieldBar (M * p)` such that
--
--   $$\mathrm{heckeDivOneBar}\;\mathrm{h}\alpha\;\mathrm{h}\beta\,(\langle P \rangle) = \sum_{i < p} \langle Q_i \rangle,$$
--
--   where $\langle \cdot \rangle$ denotes the divisor `Finsupp.single _ 1` and `heckeDivOneBar` is the correspondence $\alpha_* \beta^*$ built from `heckeBetaOneBar` and `heckeAlphaOneBar` at level $M p$ and $\ell = p$ over $\overline{\mathbb{Q}}$; and moreover, for every $i$, the place $Q_i$ again satisfies the same four-clause Gauss-reduction condition ($\mathrm{i}$)–($\mathrm{iv}$), and
--
--   $$\mathrm{red}_1(Q_i) = \mathrm{frobIg}^{-1} \cdot \mathrm{red}_1(P).$$
--
--   This is the place-level form of the Eichler–Shimura congruence $U_p = V$ on the Igusa component of $X_1(Mp)$ in characteristic $p$: the level-$p$ Hecke correspondence takes a place reducing into the component $C_1$, inside the finite $j$-chart and away from the nodes, to a sum of $p$ places of the same kind, each reducing to the inverse-Frobenius translate of the reduction of the original place. It feeds the two computations of the components of the Néron special-fibre projection for Hecke-translated degree-zero classes of $X_1(Mp)$, namely [`ModularCurve.XOneP.addEquiv_proj_fst_eq_natCast_smul_frob_inv_smul_of_pts_reduction_heckeGenOne_of_points_pic0Mk_valuationSubring_of_forall_mem_support_gaussReduces_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.addEquiv_proj_fst_eq_natCast_smul_frob_inv_smul_of_pts_reduction_heckeGenOne_of_points_pic0Mk_valuationSubring_of_forall_mem_support_gaussReduces_twoChartModel_x1_mul) and [`ModularCurve.XOneP.proj_snd_eq_zero_of_pts_reduction_heckeGenOne_of_points_pic0Mk_valuationSubring_of_forall_mem_support_gaussReduces_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.proj_snd_eq_zero_of_pts_reduction_heckeGenOne_of_points_pic0Mk_valuationSubring_of_forall_mem_support_gaussReduces_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
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

theorem ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_twoChartModel_x1_mul
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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk)

    (red₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
      AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hred₁ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
        (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
      red₁ P = Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩)

    (hOPl : Pl.toSubring ≤ O)

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hα : ModularCurve.HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    (hβ : ModularCurve.HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))]

    (hdeg : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p) = p) :

    ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
      (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
         (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
        Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
          (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
        c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
          Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
        (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
        ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →

      ∃ Q : Fin p → AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)),
        ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ (Finsupp.single P 1) =
          ∑ i : Fin p, Finsupp.single (Q i) 1 ∧
        ∀ i : Fin p,
          (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
             (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
            Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
              (Mη.pointEquivPlace.symm (Q i)).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
            c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
              Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
            (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
            ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
              Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) ∧
          red₁ (Q i) = frobIg⁻¹ • red₁ P := by sorry
