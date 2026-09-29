-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_nodeEquation_jWidth_of_eq_zero_or_eq_1728_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeCoordinates_nodeEquation_jWidth_of_eq_zero_or_eq_1728_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/f4abd364-292f-5dbc-a1bc-faf7e6684ce8
-- title:
--   Node coordinates at wide supersingular crossings, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, data `data` consisting of a monic bivariate modular polynomial $\Phi$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, together with the Kronecker congruence `hKr` asserting that $\Phi$ reduced modulo $q$ equals $(C X^q - X)(C X - X^q)$, and the integrality hypotheses $h\alpha$, $h\beta$ on the two Hecke maps from level $1$ to level $q$; let $P$ be a `PlaceSpecialization` for these data and $R$ a `ProlongationTuple` over $P$. Assume: $\mathrm{red}$ has kernel exactly the maximal ideal of $A$; $q \ge 5$; $R$ satisfies `IsModel`, that is the two divisor laws and the two cusp laws; $W$ is a finite set of places of the level-one geometric modular function field over $k$, each of which is supersingular (rational, with $j$ and $j_N$ in its valuation ring, and with $j$-value in $\mathrm{ssJSet}\ q\ k$); $R$ satisfies the regularity law and the node-value law for $W$. Let $w \in W$ be fixed by the square of the arithmetic Frobenius semilinear automorphism, with $j$-value $\mathrm{eval}_w(j) = a$ where $a = 0$ or $a = 1728$. Let $K \subset \overline{\mathbf Q}$ be a finite extension of $\mathbf Q$, let $\varpi$ lie in the coefficient ring $A \cap K$ and generate the kernel of the restricted reduction map on $A \cap K$ (every element killed by it is a multiple of $\varpi$), and let $q = \varpi^{e_K}\varepsilon$ with $\varepsilon$ a unit of $A \cap K$. The conclusion: there exist node coordinates $c = (x,y)$ in $R$'s ring of functions over $K$ at $w$ — both $x$ and $y$ integral for the two prolongations $R_1$, $R_2$ and for every place above $w$ under `reduceFst`, and lying in the subfield generated over $K$-constants by $j$ and $j_q$, with $\mathrm{res}_1(x) = 0$, $\mathrm{ord}_{\varphi w}(\mathrm{res}_2(x)) = 1$, $\mathrm{res}_2(y) = 0$, $\mathrm{ord}_w(\mathrm{res}_1(y)) = 1$ — and a unit $u$ of that ring such that $x\,y = (\varpi)^{\,\mathrm{jWidth}(a)\,e_K}\,u$, where $\varpi$ is viewed as a constant function via `nodeConst` and $\mathrm{jWidth}(a)$ is $3$ for $a = 0$ and $2$ for $a = 1728$.
--
--   This is the wide-value companion of the generic node-coordinate statement: at a supersingular point of the level-one model of $X_0(q)$ whose $j$-invariant is $0$ or $1728$, the crossing of the two components is an $A_3$- or $A_2$-type singularity, and the product of the two local coordinates acquires the corresponding Deligne–Rapoport width in the exponent of the uniformiser of the prescribed coefficient field $K$. It is used in the passage to inertia-fixed presentations of the node at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_nodeEquation_jWidth_of_eq_zero_or_eq_1728_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeCoordinates_nodeEquation_jWidth_of_eq_zero_or_eq_1728_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ W)
    (hfix : arithFrobC q k 1 • (arithFrobC q k 1 • w) = w)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (hwide : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) :
    ∃ (c : R.NodeCoordinates K w) (u : ↥(R.nodeIntegersOver K w)),
      IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ (jWidth a * eK) * u := by sorry
