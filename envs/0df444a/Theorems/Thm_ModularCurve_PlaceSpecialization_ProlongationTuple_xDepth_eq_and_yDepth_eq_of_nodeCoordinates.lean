-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_xDepth_eq_and_yDepth_eq_of_nodeCoordinates
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.xDepth_eq_and_yDepth_eq_of_nodeCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/1a1774a7-8445-5722-a8ff-5646fa51e3b6
-- title:
--   Node depths are independent of the chosen presentation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$ with a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two degeneracy maps $\overline{\alpha},\overline{\beta}$ from level $N$ to level $Nq$, a place specialisation $P$ and a prolongation tuple $R$ over $P$, and assume $q \nmid N$. Assume $R$ is a model (the two divisor laws and the two cusp laws hold), and let $W$ be a finite set of places of `modularFunctionFieldC k N` each of which is supersingular (rational, affine in $j$ and $j_N$, with $j$-value in the supersingular set), such that $R$ satisfies the regularity law and the node value law for $W$. Let $w \in W$ and assume the value integrality law at $w$: every $f$ in the node integer ring at $w$ has $V(f)$-evaluation lying in $A$ for every place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$. Let $K$ be a finite extension of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ and $c$ a node coordinate datum at $w$ over $K$ (elements $x,y$ of the ring of node integers defined over $K$ with $\mathrm{res}_1(x)=0$, $\mathrm{ord}$ of $\mathrm{res}_2(x)$ at the arithmetic‑Frobenius translate of $w$ equal to $1$, $\mathrm{res}_2(y)=0$, and $\mathrm{ord}_w(\mathrm{res}_1(y))=1$), and suppose $x\,y = (\mathrm{nodeConst}_K\,\varpi)^E u$ for some $\varpi \in A \cap K$, some $E \in \mathbb{N}$ and some unit $u$ of that ring. Let $K_0$ be another finite extension of $\mathbb{Q}$, $c_1$ a node coordinate datum at $w$ over $K_0$ with $x_1 y_1 = (\mathrm{nodeConst}_{K_0}\,q)^{E_0} u_0$ for some $E_0$ and some unit $u_0$. Then for every place $V$ with $P.\mathrm{reduceFst}\,V = w$ the $A$-valuations of the $V$-evaluations agree coordinatewise: $\mathrm{xDepth}_c(V) = \mathrm{xDepth}_{c_1}(V)$ and $\mathrm{yDepth}_c(V) = \mathrm{yDepth}_{c_1}(V)$.
--
--   This is the presentation-invariance of the local node invariants at a supersingular point of the special fibre of the level-$Nq$ modular curve: the depths of the two branch parameters, measured by the valuation of $A$ at a place above $w$, do not depend on the coefficient field over which the node coordinates are defined, nor on the local node equation $xy = \varpi^E u$ chosen to present them. It is used in the construction and comparison of resolved model packages at level $N$, where node charts over varying finite coefficient fields must be matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_xDepth_eq_and_yDepth_eq_of_nodeCoordinates.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.xDepth_eq_and_yDepth_eq_of_nodeCoordinates
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    (c₁ : R.NodeCoordinates K₀ w)
    (E₀ : ℕ) (u₀ : ↥(R.nodeIntegersOver K₀ w)) (hu₀ : IsUnit u₀)
    (hxy₁ : c₁.x * c₁.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ * u₀)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hVw : P.reduceFst V = w) :
    c.xDepth V = c₁.xDepth V ∧ c.yDepth V = c₁.yDepth V := by sorry
