-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts
-- name    : ModularCurve.PlaceSpecialization.localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/0d1b9c50-a4a5-58d4-b9c7-0b84e2ac9861
-- title:
--   Local semicontinuity from reduced divisors, coordinates and charts
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, a positive level $N$, a field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, data `data` for the modular polynomial $\Phi$ of level $q$ satisfying the Kronecker congruence $\Phi \equiv (X'^q - X)(X' - X^q)$ mod $q$, the integrality hypotheses $h\alpha$, $h\beta$ asserting that the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbf Q}$ are integral ring homomorphisms, a place specialisation $P$ for these data, and a prolongation tuple $R$ over $P$ (so a pair $R_1$, $R_2$ of regular prolongations of $A$ to the level-$Nq$ field $\overline{\mathbf Q}$-field, with residue field comparisons $\iota$, `redBar` and the Atkin–Lehner identification of the second residue with the first). Assume $q \nmid N$; that $P$ reduces divisors, i.e. for every level-$N$ function $f$ whose Laurent expansion lies in `CharPReduction.modularLocalized` with nonzero reduction in `modularFunctionFieldC k N`, the pushforward along `P.sp` of the divisor $W \mapsto \operatorname{ord}_W f$ computes, at every place $v$ of the fibre field, $\operatorname{ord}_v$ of the reduction of $f$; that $P$ has coordinates, i.e. every place $v$ of `modularFunctionFieldC k N` admits a level-$N$ function $T$, integral with reduction in the fibre field, whose reduction is a uniformiser at $v$ after subtraction of a constant of $k$, and such that each place $u'$ above $v$ under `P.sp` has some $a \in A$ with $\operatorname{ord}_{u'}(T - a) > 0$ and $\operatorname{ord}_v(\mathrm{fibreReduction}\,T - red\,a) > 0$; and that $R$ has charts, i.e. every place $v$ of the fibre field with $\varphi^2 v \neq v$, where $\varphi =$ `frobOnPlacesGeomLevel`, carries a set $S$ of level-$Nq$ functions with `IsChartAt R v S`. The conclusion is `LocalSemicontinuity R`: for every level-$Nq$ function $f$ integral for both $R_1$ and $R_2$ with both residues nonzero, every divisor $D$ with $D\,W = \operatorname{ord}_W f$ for all places $W$, and every place $v$ of the fibre field with $\varphi^2 v \neq v$ such that $D\,W \ge 0$ at all $W$ with `P.IsStrictFst W` and `P.reduceFst` $W = v$, one has $(\,$`Finsupp.mapDomain P.reduceFst (P.fstDiv D)`$)(v) \le \operatorname{ord}_v(R.\mathrm{residue}_1 f)$, and symmetrically with `IsStrictSnd`, `reduceSnd`, `sndDiv` and $R.\mathrm{residue}_2$ for places $u$ with $\varphi^2 u \neq u$.
--
--   This is the semicontinuity estimate comparing the order of vanishing of the residue of a function along a component of the special fibre at $q$ with the sum of the orders of the function at the places of the level-$Nq$ field lying over the given place, away from the places fixed by the square of the geometric Frobenius (the supersingular crossing points being excluded in this way). It is the input used by [`ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed) in the construction of a prolongation tuple which is a model and satisfies the order law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts.lean

import Definitions.Def_ModularCurve_ChartSemicontinuity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N) (hsp : ReducesDivisors P) (hcoord : HasCoordinates P) (hchart : HasCharts R) :
    LocalSemicontinuity R := by sorry
