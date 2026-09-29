-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/557bf049-2eee-57fc-b8b7-b5ec9c105af4
-- title:
--   Node coordinate minus its value is a uniformiser
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N\ge 1$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$, a modular polynomial datum `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q-X)(Y-X^q) \bmod q$, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps at level $Nq$, a place specialisation $P$ of these data, and a prolongation tuple $R$ over $P$; assume $k$ algebraically closed, $q\nmid N$, that $R$ `IsModel` (the two divisor laws and the two cusp laws) and that $R$ satisfies `OrderLawFixed`. Let $K\subset\overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$ and $w$ a place of $\mathrm{modularFunctionFieldC}\ k\ N$ lying in $\mathrm{ssPlaces}\ q\ N\ k$, i.e. $w$ is rational, both $j$ and $j_N$ are $w$-integral, and $w(j)$ lies in the supersingular $j$-set; assume the value-integrality law at $w$: every $f$ in the node ring $\mathrm{nodeIntegers}\ w$ has $V.\mathrm{evalAt}(f)\in A$ for every place $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ with $P.\mathrm{reduceFst}\,V=w$. Let $B=R.\mathrm{nodeIntegersOver}\ K\ w$ (elements of $\mathrm{nodeIntegers}\ w$ whose Laurent expansion lies in $\mathrm{fieldOver}(Nq)\,K$), assumed local and Noetherian, and assume every $g\in B$ satisfies $g-R.\mathrm{nodeConst}\ K\ w\ o$ a non-unit for some $o$ in the coefficient ring $A\cap K$. Let $\varpi\in A\cap K$ generate the kernel of $\mathrm{redRestrict}\ \mathrm{red}\ K$ in the divisibility sense. Let $W$ be a complete discrete valuation domain, $\pi$ irreducible in $W$, $\sigma\colon W\to \widehat{B}$ a ring homomorphism with $\sigma(\pi)$ the image of $\mathrm{nodeConst}\ K\ w\ \varpi$, $E\ge 1$, and $\iota\colon \widehat{B}\xrightarrow{\ \sim\ } W[[U,V]]/(UV-\pi^{E})$ a ring isomorphism carrying $\sigma(o)$ to the constant $o$ for all $o\in W$, and reading off branch orders: if $f\in B$ has non-zero first residue of $w$-order $n$ then $\iota(f)$ is congruent to a unit times $V^{n}$ modulo $(\pi,U)$, and if $f$ has non-zero second residue of order $n$ at $\mathrm{arithFrobC}\cdot w$ then $\iota(f)$ is congruent to a unit times $U^{n}$ modulo $(\pi,V)$. Finally let $c=(x,y)$ be node coordinates over $K$ at $w$ (first residue of $x$ zero, second residue of $x$ of order $1$ at $\mathrm{arithFrobC}\cdot w$, second residue of $y$ zero, first residue of $y$ of $w$-order $1$) with $x\cdot y = (\mathrm{nodeConst}\ K\ w\ \varpi)^{E_0}u$ for some $E_0\in\mathbb{N}$ and some unit $u$ of $B$. Then for every place $V'$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V'=w$, the order of $y-V'.\mathrm{evalAt}(y)$ at $V'$ equals $1$.
--
--   This is the order law for the node annulus of $X_0(Nq)$ at a supersingular place: on each component above the node, the coordinate $y$ of a node-coordinate pair is a uniformiser after subtracting its value, the local picture attached to the equation $xy=\varpi^{E}$ of the model of $X_0(Nq)$ at a supersingular point. It is used in the construction of the annulus parametrisation, where the places above $w$ at which $y$ takes a given value are identified with the points of the corresponding annulus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem
    ModularCurve.PlaceSpecialization.ProlongationTuple.ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hvalA : R.ValueIntegralityLaw w)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) :
    ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      V'.ord ((↑c.y : ↥(modularFunctionFieldBar (N * q)))
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
              (V'.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))))) = 1 := by sorry
