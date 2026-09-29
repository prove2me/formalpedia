-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_charts_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_charts_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/8cf61a3a-7c18-567b-9be7-cde58e63edf4
-- title:
--   Depth-to-component dictionary for the resolved Deligne–Rapoport model
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, a valuation subring $A$ of $\overline{\mathbf Q}$ whose nonunits contain $q$ (the predicate `LiesOverPrime`), and a ring homomorphism $\rho$ from the base ring `DRLevel.R q` to $A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbf Q}$ is the structure map $\mathrm{R}(q) \to \overline{\mathbf Q}$. Fix a package $\mathfrak P$ of type `DRModelPackageLevel N₀ q hqN`: the Igusa scheme $X(N_0q,q)$ viewed as a proper, flat, integral, locally finitely presented scheme over $\operatorname{Spec} \mathrm{R}(q)$ with integrally closed sections on affine opens, together with a `CurveModel` `Meta` for the geometric generic fibre whose function field is identified with $\overline{\mathbf Q}$-base change `modularFunctionFieldBar (N₀ * q)` of the full modular function field, an isomorphism `eeta` of `Meta.C` with the geometric generic fibre compatible with the structure maps, Galois equivariance of the resulting bijection between $\overline{\mathbf Q}$-points and places, pinning of the finite Igusa chart algebra inside the function field, smoothness and geometric integrality of the rational generic fibre, the two cusp sections, and the remaining data of that structure. The residue field $\kappa_A$ of $A$ is assumed of characteristic $q$ and algebraically closed.
--
--   Further fixed are: modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbf Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence `hKr`, namely that the bivariate reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$; integrality hypotheses $h\alpha$, $h\beta$ asserting that the Hecke maps $\bar\alpha$, $\bar\beta$ at level $N_0$, $q$ are integral ring homomorphisms; a fibre model `fm` of type `CharPModel.FibreModel N₀ A q κ_A (residue A)`, consisting of subrings `BFin`, `BInf` of the base-changed modular function field containing the constants and the relevant $j$-functions, integral over the affine bases, together with specialisation homomorphisms `piFin`, `piInf` into `modularFunctionFieldC κ_A N₀` matching constants and $j$-functions; the cusp-chart hypothesis `cc`, which asserts that $\bar j_{N_0}\,\bar j^{-N_0}$ lies in `BInf` and that `piInf` sends it to the corresponding element of `modularFunctionFieldC κ_A N₀`; the hypotheses `hfin`, `hinf`, saying that the images under `coeffEmb` of the Igusa chart algebras `chartAlgFin N₀ q`, `chartAlgInf N₀ q` lie in `fm.BFin`, `fm.BInf`; surjectivity `hred` of the residue map of $A$; modular polynomial data `dataAll d` for every divisor $d$ of $N_0$; and separability `hsepΦ` of the image of $\Phi$ for $N_0$ in $\kappa_A(T)$ after reduction of coefficients modulo $q$.
--
--   Next, a place specialisation $P$ of type `PlaceSpecialization A q N₀ data hKr κ_A (residue A) hα hβ` is fixed, pinned by `hP` so that its place map $P.\mathrm{sp}$ coincides with `fm.spPlace hred dataAll hsepΦ`; a prolongation tuple $R$ for $P$ with `hR : R.IsModel` (the conjunction of the two divisor laws and the two cusp laws, at $\infty$ and at $0$) and `hO : R.OrderLawFixed` (for $f$ integral for both prolongations with nonzero residues, and for a divisor $D$ recording the orders $W \mapsto \operatorname{ord}_W f$, the pushforward of $D$ along $P.\mathrm{reduceFst}$ at a Frobenius-fixed affine geometric place $v$ equals $\operatorname{ord}_v$ of the first residue plus $\operatorname{ord}$ of the second residue at the Frobenius translate of $v$). A finite set $W$ of places of `modularFunctionFieldC κ_A N₀` is fixed, with `hW` stating that $W$ is exactly the set `ssPlaces q N₀ κ_A` of supersingular places, and $R$ is assumed to satisfy the regularity law `hreg` and the node value law `hval` relative to $W$ (each a two- respectively one-clause statement about residues of functions integral for both prolongations at node pairs of places, summarised here). A width function $e$ on places is given, with `he` fixing $e\,w =$ `placeWidthChar q N₀ w` for $w \in W$.
--
--   The descent data over a number field are: a finite extension $K$ of $\mathbf Q$ inside $\overline{\mathbf Q}$, an element $\varpi$ of the coefficient ring `NodeLocalized.coeffSubring A K` $= A \cap K$ with `hϖ` asserting that an element of that ring is killed by the restricted reduction map precisely when it is a multiple of $\varpi$; an integer $eK \ge 1$, a unit $\varepsilon$ of the coefficient ring, and `hqϖ` asserting $q = \varpi^{eK}\varepsilon$; node coordinates `cs w hw` over $K$ for each $w \in W$, that is, elements $x, y$ of the ring `R.nodeIntegersOver K w` with first residue of $x$ zero, $\operatorname{ord}$ of the second residue of $x$ equal to $1$ at the arithmetic-Frobenius translate of $w$, second residue of $y$ zero and $\operatorname{ord}_w$ of the first residue of $y$ equal to $1$; `hxy`, giving a unit $u$ with $xy = (\mathrm{nodeConst}\,K\,w\,\varpi)^{e(w)\,eK}\,u$; `hmax`, that the ideal generated by `nodeConst K w ϖ`, $x$, $y$ is maximal and is the only maximal ideal of `R.nodeIntegersOver K w`; `hbr`, that the ideals generated by $(\varpi, x)$ and by $(\varpi, y)$ are prime, with $y$ outside the first and $x$ outside the second; `hnoeth`, that each `R.nodeIntegersOver K w` is Noetherian; `hres`, that for every $g$ in that ring some constant `nodeConst K w o` makes $g -$ `nodeConst K w o` a nonunit; and `hVI`, the value integrality law at each $w \in W$: for $f$ in `R.nodeIntegers w` and every place $V$ of the geometric generic fibre with $P.\mathrm{reduceFst}\,V = w$, the value $V(f)$ lies in $A$.
--
--   The arithmetic base is a discrete valuation domain $O$ together with a ring isomorphism $eO$ of $O$ onto the preimage of $A$ in the field fixed by the inertia subgroup `A.inertiaSubgroupIn ℚ` (the image in $\operatorname{Aut}(\overline{\mathbf Q}/\mathbf Q)$ of the inertia subgroup of $A$), with `hϖO` stating that the maximal ideal of $O$ is generated by $q$, a homomorphism $\rho_O : \mathrm{R}(q) \to O$ compatible via `hρO` with the structure map to $\overline{\mathbf Q}$ through $eO$ and the inertia-fixed field, and a homomorphism $\mathrm{to}\kappa : O \to \kappa_A$ given by `htoκ` as the residue map of $A$ applied to the image of $eO$. Over this base, $\mathfrak X^{\mathrm{reg}}$ is a resolved model of type `DRResolvedModelPackageLevel N₀ q 𝔓 O ρO κ_A toκ`: a scheme $Y$, proper, flat and integral over $\operatorname{Spec} O$, locally Noetherian, with a proper map `toDR` to the base change `XO` of the Deligne–Rapoport model, regular with stalk Krull dimension at most $2$ at the points of the fibre over $q$, with `toDR` an isomorphism over the smooth locus and over the generic fibre, a finite set `node` of crossings with widths $\ge 1$, an identification `nodeEquiv` of `node` with the fibre product of the two components of $\mathfrak P$ in characteristic $q$, and invertible integral component ideal sheaves `comp v` indexed by `X0MqComponents width` whose product is the ideal generated by $q$, together with the further clauses of that structure. Crossing charts are provided by a family `Fc` of ideal sheaf data on the crossing resolutions, the hypothesis `hF` computing their restriction along the chart immersion `Resolution.ι` as the explicit ideal generated by $V$, by $U$, or the unit ideal according as the component index equals $i$, $i+1$, or neither, and `ch`, a `DRResolvedModelChartsLevelRam` structure for the unramified-to-ramified reading of $\mathfrak X^{\mathrm{reg}}$ relative to `Fc`: étale maps from opens around each crossing point to the crossing scheme of $\varpi^{\text{width}}$, pullback isomorphisms onto the preimages in $Y$, and the labelling of the components `comp (chainPos …)` by `Fc`. The crossings are indexed by $W$ through a bijection $\sigma_N : W \simeq \mathfrak X^{\mathrm{reg}}.\mathrm{node}$, with `hσN_pin` asserting that the supersingular place attached to the node $\sigma_N(w)$ by `𝔓.nodeEquiv` is $w$ itself.
--
--   Finally, an orientation bit `swap : Bool` is fixed, pinned by the hypothesis `hswap`: for every place $V$ of `modularFunctionFieldBar (N₀ * q)` fixed by the inertia subgroup of $A$ acting through `arithmeticGalois`, and every section $s$ of the base-changed model, i.e. $s : \operatorname{Spec} O \to$ `pullback (DRLevel.toBase N₀ q) (Spec.map ρO)` with $s$ followed by `pullback.snd` the identity, such that Spec of the composite ring map $O \to \overline{\mathbf Q}$ followed by $s$ followed by `pullback.fst` is the $\overline{\mathbf Q}$-point `Meta.pointEquivPlace.symm V` followed by `eeta` followed by `pullback.fst`: if $P.\mathrm{IsStrictFst}\,V$ holds (the Frobenius image of $P.\mathrm{reduceFst}\,V$ is $P.\mathrm{reduceSnd}\,V$, and the double Frobenius image of $P.\mathrm{reduceFst}\,V$ differs from it) then the image of the closed point of $\operatorname{Spec} O$ under $s$ lies in the range of the base map of the component indexed by $1$ if `swap` and by $0$ otherwise, composed with `DRLevel.bcMap ρO toκ`, and not in the range for the other index; and symmetrically, if $P.\mathrm{IsStrictSnd}\,V$ holds then the closed point lies in the range for the index $0$ if `swap` and $1$ otherwise, and not in the range for the other.
--
--   Under these hypotheses there exist a finite extension $K_0$ of $\mathbf Q$ inside $\overline{\mathbf Q}$, node coordinates $c_1(w)$ over $K_0$ for every $w \in W$, a function $E_0 : W \to \mathbf N$ and elements $u_0(w)$ of `R.nodeIntegersOver K₀ w` for $w \in W$, such that the following hold (the existential statement lists these data together with the stated properties and ends with `True`).
--
--   First, each $u_0(w)$ is a unit, and the coordinates factor the uniformiser: $x_{c_1(w)}\,y_{c_1(w)} = (\mathrm{nodeConst}\,K_0\,w\,(q : \mathrm{coeffSubring}\,A\,K_0))^{E_0(w)}\,u_0(w)$; so the exponent is taken with respect to $q$ itself rather than a uniformiser of $K_0$.
--
--   Second (the clause `hdepth_eq`), the depths are unchanged by the descent: for every $w \in W$ and every place $V$ of `modularFunctionFieldBar (N₀ * q)` with $P.\mathrm{reduceFst}\,V = w$, the $A$-valuations $V(x)$ and $V(y)$ computed from the given coordinates `cs w hw` and from the new coordinates $c_1(w)$ agree, i.e. `xDepth` and `yDepth` coincide.
--
--   Third (the clause `hchart`), the dictionary between depth and component: for every $w \in W$, every place $V$ with $P.\mathrm{reduceFst}\,V = w$ which is fixed by the inertia subgroup of $A$ acting through `arithmeticGalois`, every section $t : \operatorname{Spec} O \to \mathfrak X^{\mathrm{reg}}.Y$ with $t$ followed by $\mathfrak X^{\mathrm{reg}}.\mathrm{toBase}$ the identity, such that Spec of the composite ring map $O \to \overline{\mathbf Q}$ followed by $t$, then `toDR`, then `pullback.fst`, equals the $\overline{\mathbf Q}$-point `Meta.pointEquivPlace.symm V` followed by `eeta` and `pullback.fst`, and every natural number $d$ with $\mathrm{yDepth}_{c_1(w)}(V) = v_A(q)^d$, and every component index $v$ of type `X0MqComponents 𝔛reg.width`: the image under $t$ of the closed point of $\operatorname{Spec} O$ lies in the support of the component ideal sheaf $\mathfrak X^{\mathrm{reg}}.\mathrm{comp}\,v$ if and only if $v =$ `chainPos 𝔛reg.width (σN w) d'`, where $d' = \mathfrak X^{\mathrm{reg}}.\mathrm{width}(\sigma_N(w)) - d$ if `swap` and $d' = d$ otherwise; here `chainPos width n d` is the first end component for $d = 0$, the $(d-1)$-st intermediate component of the chain at the node $n$ for $0 < d < \mathrm{width}(n)$, and the second end component otherwise.
--
--   This is the level-$\Gamma_0(N_0q)$ form of the dictionary translating the $y$-depth of a section at a supersingular crossing into the component of the special fibre of a resolved Deligne–Rapoport model on which the section's closed point lies, together with a descent of the node coordinates to a number field in which the factorisation $xy = q^{E_0}u$ holds with $q$ itself. It is the final existential block consumed by [`ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace`](thm.html#ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace), which assembles the resolved model together with its node indexing and orientation bit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_charts_of_sp_eq_spPlace.lean

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
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRModelPackageLevel.exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_charts_of_sp_eq_spPlace

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
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackageLevel N₀ q 𝔓 O ρO (ResidueField ↥A) toκ)

    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ((q : ℕ) : O) e).IdealSheafData) (hF : ∀ (e : ℕ) (i : Fin e) (k' : Fin (e + 1)), (Fc e k').comap (Resolution.ι ((q : ℕ) : O) e i) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ((q : ℕ) : O)))).inv.hom
          (if (k' : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ((q : ℕ) : O)} else if (k' : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ((q : ℕ) : O)}
            else ⊤)))
    (ch : (DRResolvedModelPackageLevelRam.ofUnramified 𝔛reg).DRResolvedModelChartsLevelRam Fc)

    (σN : ↥W ≃ 𝔛reg.node)
    (hσN_pin : ∀ w : ↥W, ((𝔓.nodeEquiv (ResidueField ↥A) (toκ.comp ρO) (𝔛reg.nodeEquiv (σN w)) : ↥(ssPlaces q N₀ (ResidueField ↥A))) : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) = (w : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)))

    (swap : Bool)
    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base)) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀)
    (c₁ : ∀ w ∈ W, R.NodeCoordinates K₀ w)
    (E₀ : ↥W → ℕ) (u₀ : ∀ w (hw : w ∈ W), ↥(R.nodeIntegersOver K₀ w)) (hu₀ : ∀ w hw, IsUnit (u₀ w hw))
    (hxy₁ : ∀ w (hw : w ∈ W), (c₁ w hw).x * (c₁ w hw).y =
      R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ ⟨w, hw⟩ * u₀ w hw)
    (hdepth_eq : ∀ w (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))), P.reduceFst V = w →
      (cs w hw).xDepth V = (c₁ w hw).xDepth V ∧ (cs w hw).yDepth V = (c₁ w hw).yDepth V)
    (hchart : ∀ w (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))), P.reduceFst V = w →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ t ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        ∀ d : ℕ, (c₁ w hw).yDepth V = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ d →
          ∀ v : X0MqComponents 𝔛reg.width,
            t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp v).support ↔
              v = DRResolvedModelPackageLevel.chainPos 𝔛reg.width (σN ⟨w, hw⟩) (if swap then 𝔛reg.width (σN ⟨w, hw⟩) - d else d)),
    True := by sorry
