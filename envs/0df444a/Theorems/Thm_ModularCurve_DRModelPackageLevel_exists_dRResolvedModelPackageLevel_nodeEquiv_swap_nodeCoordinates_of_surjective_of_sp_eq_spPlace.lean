-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/9356b482-ac0d-5712-a532-89bc93d48838
-- title:
--   Existence of a resolved Deligne–Rapoport model with place–component dictionary
-- statement:
--   Throughout, $N_0\ge 1$ and $q$ is a prime with $q\nmid N_0$; $A$ is a valuation subring of $\overline{\mathbf Q}$ with $q$ a non‑unit of $A$ (`hA : A.LiesOverPrime q`), and $\rho$ is a ring homomorphism from the base ring `DRLevel.R q` to $A$ whose composite with the inclusion $A\hookrightarrow\overline{\mathbf Q}$ is the canonical algebra map (`hρ`). The residue field $\kappa_A=$ `ResidueField ↥A` is assumed to be of characteristic $q$ and algebraically closed. Further, $\mathfrak P$ is a Deligne–Rapoport model package of level $N_0q$ at $q$ (`DRModelPackageLevel N₀ q hqN`): a proper, flat, integral, locally finitely presented and normal scheme over `Spec (DRLevel.R q)` together with a curve model `Meta` of the base‑changed modular function field $\overline{\mathbf Q}\cdot F(N_0q)$, an isomorphism `eeta` of `Meta.C` with the pullback of the model along $\operatorname{Spec}$ of `algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)` over the base, equivariance of the identification of points with places under the arithmetic Galois action, pinning of the Igusa charts, smoothness and geometric integrality of the generic fibre, and cusp sections.
--
--   The remaining input is organised in groups.
--
--   *Modular‑polynomial and Hecke data.* `data : ModularPolynomialData q` is a monic $\Phi\in\mathbf Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$; `hKr` is the Kronecker congruence $\Phi\equiv (X^q-Y)(X-Y^q)$ modulo $q$ in the bivariate reduction; `hα`, `hβ` assert that the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $N_0$ and $q$ are integral ring homomorphisms.
--
--   *Fibre model at $q$.* `fm` is a fibre model of level $N_0$ for $A$, $q$ and the reduction `residue ↥A`: two subrings $B_{\mathrm{fin}}$, $B_\infty$ of the base‑changed modular function field containing the constants and the relevant $j$‑expressions, integral over the affine bases, with reduction homomorphisms $\pi_{\mathrm{fin}}$, $\pi_\infty$ into `modularFunctionFieldC κ_A N₀` compatible with constants and with $j$, $j_N$. `cc : fm.CuspChart` adds that $\bar j_N\cdot\bar j^{-N_0}$ lies in $B_\infty$ and reduces to the corresponding element of the characteristic‑$q$ function field. `hfin` and `hinf` require that every element of the Igusa chart algebras `IgusaScheme.chartAlgFin N₀ q` and `IgusaScheme.chartAlgInf N₀ q`, transported by the coefficient embedding, lies in $B_{\mathrm{fin}}$, resp. $B_\infty$. `hred` asserts that `residue ↥A` is surjective; `dataAll` provides modular‑polynomial data for every divisor $d$ of $N_0$; `hsepΦ` asserts that $\Phi$ for $N_0$, reduced modulo $q$ and viewed over `RatFunc κ_A`, is separable.
--
--   *Specialisation and prolongation.* $P$ is a place specialisation for $A$, $q$, $N_0$, `data`, `hKr`, $\kappa_A$ and `residue ↥A`, consisting of a map `sp` from places of $\overline{\mathbf Q}\cdot F(N_0)$ to places of `modularFunctionFieldC κ_A N₀`, a homomorphism on degree‑zero divisor classes, and the compatibility laws at $j$, $j_N$ and the cusps; `hP` pins `P.sp` to the specialisation map `fm.spPlace hred dataAll hsepΦ` of the fibre model. $R$ is a prolongation tuple for $P$ (two regular prolongations $R_1,R_2$ of the level‑$N_0q$ function field with their residue maps and Atkin–Lehner compatibility). `hR : R.IsModel` is the conjunction of the two divisor laws and the two cusp laws; `hO : R.OrderLawFixed` states that for $f$ with non‑zero residues under both prolongations and $D$ the divisor of $f$, at every affine geometric place $v$ fixed by the square of the geometric Frobenius the multiplicity of $v$ in $P.\mathrm{reduceFst}_*D$ equals $\operatorname{ord}_v$ of the first residue plus $\operatorname{ord}_{\mathrm{Frob}\,v}$ of the second. $W$ is a finite set of places with `hW` saying that $W$ consists exactly of the supersingular places `ssPlaces q N₀ κ_A`; `hreg : R.RegularityLaw W` and `hval : R.NodeValueLaw W` are the regularity law (non‑negativity of the residues' orders, and existence of common values at the Frobenius node pairs of $W$) and the node‑value law (existence of a common non‑zero value of the two residues at node pairs avoided by the divisor of $f$).
--
--   *Width datum.* $e$ is a function on places with `he : e w = placeWidthChar q N₀ w` for $w\in W$, that is $e(w)=\mathrm{jWidthChar}(q,w(j))/\mathrm{placeRamificationJ}(N_0,w)$.
--
--   *Uniformiser data over a number field.* $K$ is a finite extension of $\mathbf Q$ inside $\overline{\mathbf Q}$, $\varpi\in A\cap K$ with `hϖ` saying that an element of $A\cap K$ has zero image under the restricted reduction precisely when it is a multiple of $\varpi$; $e_K\ge 1$, $\varepsilon$ a unit of $A\cap K$, and `hqϖ : q = ϖ^eK * ε`.
--
--   *Node coordinates.* For each $w\in W$, `cs w` is a system of node coordinates over $K$: elements $x,y$ of the node ring `R.nodeIntegersOver K w` with first residue of $x$ zero, order one of the second residue of $x$ at the Frobenius translate of $w$, second residue of $y$ zero and $\operatorname{ord}_w$ of the first residue of $y$ equal to one. The crossing relation `hxy` gives a unit $u$ with $xy=\mathrm{nodeConst}(\varpi)^{e(w)e_K}u$; `hmax` asserts that the ideal generated by $\mathrm{nodeConst}(\varpi),x,y$ is maximal and is the only maximal ideal of the node ring; `hbr` asserts that the ideals generated by $\mathrm{nodeConst}(\varpi),x$ and by $\mathrm{nodeConst}(\varpi),y$ are prime, with $y$ outside the first and $x$ outside the second; `hnoeth` asserts that each node ring is Noetherian; `hres` asserts that for every $g$ in a node ring some constant $\mathrm{nodeConst}(o)$, $o\in A\cap K$, makes $g-\mathrm{nodeConst}(o)$ a non‑unit; `hVI` asserts the value‑integrality law at each $w\in W$, namely that elements of `R.nodeIntegers w` take values in $A$ at every place $V$ of $\overline{\mathbf Q}\cdot F(N_0q)$ with $P.\mathrm{reduceFst}\,V=w$.
--
--   Write $\mathcal O$ for `A.comap` of the algebra map from the fixed field of `A.inertiaSubgroupIn ℚ` (the image in $\operatorname{Aut}(\overline{\mathbf Q}/\mathbf Q)$ of the inertia subgroup of $A$) into $\overline{\mathbf Q}$, i.e. for the valuation ring induced by $A$ on the inertia‑fixed field. The conclusion asserts the existence of the following data and properties, the body of the nested existential being `True`, so that the content of the theorem is exactly the existence of the tuple.
--
--   (1) A proof that $\mathcal O$ is a discrete valuation ring, and (2) `hϖO`: its maximal ideal is generated by $q$.
--
--   (3) A ring homomorphism $\rho_{\mathcal O}$ from `DRLevel.R q` to $\mathcal O$ with (4) `hρO`: the composite of $\rho_{\mathcal O}$ with $\mathcal O\hookrightarrow$ inertia‑fixed field $\hookrightarrow\overline{\mathbf Q}$ is `algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)`.
--
--   (5) A ring homomorphism `toκ` from $\mathcal O$ to $\kappa_A$ with (6) `htoκ`: `toκ o` is the residue in $\kappa_A$ of the element of $A$ given by the image of $o$ in $\overline{\mathbf Q}$.
--
--   (7) An inhabitant $\mathfrak X^{\mathrm{reg}}$ of `DRResolvedModelPackageLevel N₀ q 𝔓 𝒪 ρO κ_A toκ`: a scheme $Y$, proper and flat over $\operatorname{Spec}\mathcal O$, integral, locally Noetherian, with a proper morphism `toDR` to the base change of the package along $\rho_{\mathcal O}$ over the base, regular with stalk Krull dimension at most two at all points above $q$, an isomorphism over the smooth locus and over the generic fibre, a finite type of nodes with widths $\ge 1$, an equivalence `nodeEquiv` of the node type with the fibre product of `𝔓.comp κ_A (toκ.comp ρO) 0` and `𝔓.comp κ_A (toκ.comp ρO) 1`, and an invertible, integral family of component ideal sheaves indexed by `X0MqComponents width` $=\mathbf{Fin}\,2\sqcup\coprod_n\mathbf{Fin}(\mathrm{width}(n)-1)$ whose product is the ideal generated by $q$, supported above $q$, together with generic points of the components.
--
--   (8) A bijection $\sigma_N$ from $W$ onto the node type of $\mathfrak X^{\mathrm{reg}}$ with (9) `hσN`: $\mathfrak X^{\mathrm{reg}}.\mathrm{width}(\sigma_N w)=e(w)$ for all $w\in W$.
--
--   (10) `hnodePt`: for every place $V$ of $\overline{\mathbf Q}\cdot F(N_0q)$ with $P.\mathrm{reduceFst}\,V\in W$, fixed by the arithmetic Galois action of every $\sigma$ in `A.inertiaSubgroupIn ℚ`, satisfying neither `P.IsStrictFst V` (Frobenius carries $\mathrm{reduceFst}\,V$ to $\mathrm{reduceSnd}\,V$ while its square moves $\mathrm{reduceFst}\,V$) nor `P.IsStrictSnd V` (the mirror condition), and for every section $s$ of the second projection of the pullback of `DRLevel.toBase N₀ q` along $\operatorname{Spec}$ of $\rho_{\mathcal O}$ over $\operatorname{Spec}\mathcal O$ such that $\operatorname{Spec}$ of the inclusion $\mathcal O\to\overline{\mathbf Q}$ followed by $s$ followed by the first projection equals the point of the package attached to $V$ through `𝔓.Meta.pointEquivPlace.symm` followed by `𝔓.eeta` and the first projection: the image under $s$ of the closed point of $\mathcal O$ is the image of $\mathfrak X^{\mathrm{reg}}.\mathrm{nodeEquiv}(\sigma_N\langle P.\mathrm{reduceFst}\,V\rangle)$ under the first projection of the fibre product of the two `𝔓.comp` morphisms followed by `𝔓.comp κ_A (toκ.comp ρO) 0` and by `DRLevel.bcMap ρO toκ`.
--
--   (11) A Boolean `swap` and (12) `hswap`: for every inertia‑fixed place $V$ as above and every section $s$ satisfying the same compatibility, if `P.IsStrictFst V` holds then the image of the closed point lies in the set‑theoretic range of (`𝔓.comp … 1` if `swap`, else `𝔓.comp … 0`) followed by `DRLevel.bcMap ρO toκ` and not in the range of the other, and if `P.IsStrictSnd V` holds then it lies in the range of (`𝔓.comp … 0` if `swap`, else `𝔓.comp … 1`) followed by `DRLevel.bcMap ρO toκ` and not in the range of the other.
--
--   (13) A further finite extension $K_0$ of $\mathbf Q$ in $\overline{\mathbf Q}$, node coordinates $c_1(w)$ over $K_0$ for each $w\in W$, exponents $E_0:W\to\mathbf N$ and units $u_0(w)$ with (14) `hxy₁`: $c_1(w).x\,c_1(w).y=\mathrm{nodeConst}_{K_0}(q)^{E_0(w)}u_0(w)$, so that over $K_0$ the crossing parameter is $q$ itself.
--
--   (15) `hdepth_eq`: for all $w\in W$ and all places $V$ with $P.\mathrm{reduceFst}\,V=w$, the $x$‑ and $y$‑depths $A$‑valuations of the coordinates `cs w` at $V$ coincide with those of $c_1(w)$.
--
--   (16) `hchart`: for all $w\in W$, all places $V$ with $P.\mathrm{reduceFst}\,V=w$ fixed by the inertia action, every section $t$ of $\mathfrak X^{\mathrm{reg}}.\mathrm{toBase}$ over $\operatorname{Spec}\mathcal O$ such that $\operatorname{Spec}$ of the inclusion $\mathcal O\to\overline{\mathbf Q}$ followed by $t$, by $\mathfrak X^{\mathrm{reg}}.\mathrm{toDR}$ and by the first projection equals the point attached to $V$, and every $d\in\mathbf N$ with $c_1(w).\mathrm{yDepth}(V)=A$‑valuation of $q$ raised to the power $d$: for every component index $v$ of `X0MqComponents 𝔛reg.width`, the image under $t$ of the closed point of $\mathcal O$ lies in the support of $\mathfrak X^{\mathrm{reg}}.\mathrm{comp}\,v$ if and only if $v=\mathrm{chainPos}(\mathrm{width},\sigma_N(w),d')$ where $d'=\mathrm{width}(\sigma_N(w))-d$ if `swap` and $d'=d$ otherwise; here $\mathrm{chainPos}$ sends $d'=0$ to the first of the two end components, $0<d'<\mathrm{width}(n)$ to the $(d'-1)$‑st interior component of the chain over the node $n$, and $d'\ge\mathrm{width}(n)$ to the second end component.
--
--   This is the production step for the resolved Deligne–Rapoport model of $X_0(N_0q)$ over the valuation ring of the inertia‑fixed field at a prime $q\nmid N_0$: from a fibre model, a place specialisation and node coordinates at the supersingular places it produces the regular model, its chain of components above $q$, and the dictionary matching supersingular places with nodes, chart positions with depths of the node coordinates, and the two branches through a node with the two degeneracy maps. It is used by [`ModularCurve.DRModelPackageLevel.comp_eq_zero_of_exists_schemeHomOver_of_depthCompLaw_of_abelJacobiPin_of_surjective_red_of_sp_eq_spPlace`](thm.html#ModularCurve.DRModelPackageLevel.comp_eq_zero_of_exists_schemeHomOver_of_depthCompLaw_of_abelJacobiPin_of_surjective_red_of_sp_eq_spPlace), where the component dictionary feeds the analysis of the special fibre of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ q}

    (fm : CharPModel.FibreModel N₀ A q (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart)
    (hfin : ∀ b : IgusaScheme.chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
    (hinf : ∀ b : IgusaScheme.chartAlgInf N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BInf)
    (hred : Function.Surjective (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N₀ → ModularPolynomialData d)
    (hsepΦ : (((dataAll N₀ (dvd_refl N₀)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (P : PlaceSpecialization A q N₀ data hKr (ResidueField ↥A) (residue ↥A) hα hβ)
    (hP : P.sp = fm.spPlace hred dataAll hsepΦ)
    (R : ProlongationTuple P)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N₀ (ResidueField ↥A))
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)

    (e : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) → ℕ) (he : ∀ w ∈ W, e w = placeWidthChar q N₀ w)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict (residue ↥A) K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (cs : ∀ w ∈ W, R.NodeCoordinates K w)
    (hxy : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
        (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u)
    (hmax : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y})
    (hbr : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
        (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w) :

    ∃ (_hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) = Ideal.span {((q : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))})
    (ρO : DRLevel.R q →+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) →+* (ResidueField ↥A))
    (htoκ : ∀ o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (((RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), ((RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) o).2⟩)

    (𝔛reg : DRResolvedModelPackageLevel N₀ q 𝔓 ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ρO (ResidueField ↥A) toκ)

    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)))

    (hnodePt : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (hw : P.reduceFst V ∈ W),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      ∀ s : Spec (CommRingCat.of ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        s.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) =
          (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv (σN ⟨P.reduceFst V, hw⟩)))

    (swap : Bool)
    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∈ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∉ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∈ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∉ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base))

    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀)
    (c₁ : ∀ w ∈ W, R.NodeCoordinates K₀ w)
    (E₀ : ↥W → ℕ) (u₀ : ∀ w (hw : w ∈ W), ↥(R.nodeIntegersOver K₀ w)) (hu₀ : ∀ w hw, IsUnit (u₀ w hw))
    (hxy₁ : ∀ w (hw : w ∈ W), (c₁ w hw).x * (c₁ w hw).y =
      R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ ⟨w, hw⟩ * u₀ w hw)
    (hdepth_eq : ∀ w (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))), P.reduceFst V = w →
      (cs w hw).xDepth V = (c₁ w hw).xDepth V ∧ (cs w hw).yDepth V = (c₁ w hw).yDepth V)
    (hchart : ∀ w (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))), P.reduceFst V = w →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ∀ (t : Spec (CommRingCat.of ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom)))) ≫ t ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        ∀ d : ℕ, (c₁ w hw).yDepth V = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ d →
          ∀ v : X0MqComponents 𝔛reg.width,
            t.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∈ (𝔛reg.comp v).support ↔
              v = DRResolvedModelPackageLevel.chainPos 𝔛reg.width (σN ⟨w, hw⟩) (if swap then 𝔛reg.width (σN ⟨w, hw⟩) - d else d)),
    True := by sorry
