-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/b714da46-f13f-5669-b04e-2b7562647353
-- title:
--   Value integrality at supersingular nodes from the fixed-place order law
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$, together with modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), a proof `hKr` of the Kronecker congruence that the reduction of $\Phi$ modulo $q$ factors as $(X^q - Y)(X - Y^q)$, and proofs `hα`, `hβ` that the two Hecke homomorphisms $\overline{\alpha}, \overline{\beta}$ at level $N$ and prime $q$ are integral ring maps. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, consisting of a lift $\overline{\mathrm{red}}$ of $\mathrm{red}$ on the residue field of $A$, an embedding of reduced function fields, and two regular prolongations $R_1, R_2$ of $A$ to $\overline{\mathbb{Q}}$-function field of level $Nq$ characterised by the localised modular reduction and its Atkin–Lehner twist. Assume $k$ is algebraically closed with decidable equality, $q \nmid N$, and that $R$ satisfies the project's predicate `OrderLawFixed`: for every $f$ integral for both $R_1$ and $R_2$ with both residues nonzero, every divisor $D$ with $D(W) = \operatorname{ord}_W f$, and every place $v$ of $k(X_0(N))$ fixed by the square of `frobOnPlacesGeomLevel` and satisfying `IsAffineGeomPlace`, the pushforward $(\,P.\mathrm{reduceFst}\,)_* D$ at $v$ equals $\operatorname{ord}_v$ of the first residue plus $\operatorname{ord}$ at the Frobenius image of $v$ of the second residue. Then for every place $w$ of `modularFunctionFieldC k N` lying in `ssPlaces q N k`, i.e. satisfying the project's supersingularity predicate, the conclusion `R.ValueIntegralityLaw w` holds: every $f$ in the node ring $R.\mathrm{nodeIntegers}\,w$ and every place $V$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$ satisfy $V.\mathrm{evalAt}\,f \in A$.
--
--   This is the maximum principle on the annulus over a supersingular crossing point of $X_0(Nq)$, in fibre-sum form: integrality of the residue disc values of functions regular on the node is deduced from the order law at places fixed by the square of the geometric Frobenius. It is used downstream in the computation of crossing exponents in terms of place widths and ramification, and in the verification that divisor classes arising from the model package are good.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    R.ValueIntegralityLaw w := by sorry
