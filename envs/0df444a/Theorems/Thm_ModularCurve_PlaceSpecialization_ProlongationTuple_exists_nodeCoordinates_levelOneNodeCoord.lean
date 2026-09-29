-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeCoordinates_levelOneNodeCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/3da4481b-f0ee-53fc-a432-0c43076c8997
-- title:
--   Kronecker pair gives node coordinates at generic supersingular nodes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}:A\to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi$ in $\mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing at $(j,j_q)$) together with a proof `hKr` of the Kronecker congruence, namely that the reduction of $\Phi$ modulo $q$ equals the product of $Y^q-X$ and $Y-X^q$, proofs $h\alpha,h\beta$ that the two degeneracy maps from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral, a place specialisation $P$ of these data and a prolongation tuple $R$ over $P$. Assume $\mathrm{red}$ has kernel exactly the maximal ideal of $A$, that $q\nmid N$ and $q\ge 5$. Let $w$ be a place of $\mathrm{modularFunctionFieldC}\,k\,N$ lying in `ssPlaces q N k` (rational, affine geometric, with supersingular $j$-value), fixed by the square of the arithmetic Frobenius semilinear automorphism, and let $a=w.\mathrm{evalAt}(\mathrm{jGeomGen}\,k\,N)$ satisfy $a\neq 0$ and $a\neq 1728$. Let $K\subseteq\overline{\mathbb{Q}}$ be a number field, let $\varpi\in A\cap K$ generate the kernel of the reduction $A\cap K\to k$ (an element $d$ reduces to $0$ iff $d\in\varpi\,(A\cap K)$), and let $q=\varpi^{e_K}\varepsilon$ in $A\cap K$ with $\varepsilon$ a unit. Then there is a node-coordinate datum $c$ for $R$ over $K$ at $w$ — a pair $c.x,c.y$ in the ring $R.\mathrm{nodeIntegersOver}\,K\,w$ (elements of $\mathrm{modularFunctionFieldBar}(Nq)$ integral for $R_1$, for $R_2$ and for every place above $w$, with $q$-expansion in the $K$-node field) such that $c.x$ has first residue $0$ and second residue of order $1$ at the Frobenius translate of $w$, while $c.y$ has second residue $0$ and first residue of order $1$ at $w$ — whose coordinates are given by the Kronecker pair $c.x=j(\mathfrak{q}^q)-j(\mathfrak{q})^q$ and $c.y=j(\mathfrak{q})-j(\mathfrak{q}^q)^q$ (that is, `jQFun N q - jFun N q ^ q` and `jFun N q - jQFun N q ^ q`), and which satisfies the node equation $c.x\,c.y=(\varpi^{e_K})\cdot u$, where $\varpi$ is read in the node ring through `R.nodeConst K w` and $u$ is a unit of that ring.
--
--   This is the local node package for the special fibre of $X_0(Nq)$ at $q$: at a supersingular point with $j\notin\{0,1728\}$ the two branches cross transversally, and the explicit functions coming from the Kronecker congruence serve as local coordinates, the crossing being governed by $xy=\varpi^{e_K}\cdot(\text{unit})$. It translates the concrete Kronecker pair into the abstract node-coordinate vocabulary, and is used by the crossing-presentation results for `nodeIntegersOver` and by the construction of an inertia-fixed node presentation at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeCoordinates_levelOneNodeCoord
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (w : Place k ↥(modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) :
    ∃ c : R.NodeCoordinates K w,
      ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (jQFun N q - jFun N q ^ q) ∧
      ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (jFun N q - jQFun N q ^ q) ∧
      ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ eK * u := by sorry
