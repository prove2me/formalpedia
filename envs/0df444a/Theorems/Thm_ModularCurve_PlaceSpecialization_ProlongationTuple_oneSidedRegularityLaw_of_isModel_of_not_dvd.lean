-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_oneSidedRegularityLaw_of_isModel_of_not_dvd
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.oneSidedRegularityLaw_of_isModel_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/4f5de827-3fd7-5e55-ac19-57672622f4f1
-- title:
--   One-sided regularity law at supersingular places for models
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N$ a nonzero level, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red} : A \to k$ a ring homomorphism; let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, and let `hα`, `hβ` assert that the two Hecke homomorphisms $\bar\alpha$, $\bar\beta$ at level $N$ and prime $q$ are integral. Assume $q \nmid N$. Let $P$ be a place specialisation of these data, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ k\ N$ whose members are exactly the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple over $P$ which is a model, i.e. satisfies the two divisor laws and the cusp laws at $\infty$ and at $0$. Then $R$ satisfies the one-sided regularity law at $W$: for every $f$ in the field $\mathrm{modularFunctionFieldBar}(Nq)$ lying in the valuation rings of both regular prolongations $R.R_1$ and $R.R_2$, every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, and all divisors $D$, $E$ on $\mathrm{modularFunctionFieldBar}(Nq)$ such that every place in the support of $D$ is strict for the first or for the second component of $P$ and such that $D + (\sigma \cdot E - E)$ is the divisor of $f$, two conclusions hold. First, at every place $v$ of $\mathrm{modularFunctionFieldC}\ k\ N$ fixed by the square of the geometric-level Frobenius on places and satisfying `IsAffineGeomPlace`: if the first residue of $f$ is nonzero its order at $v$ is $\ge 0$, and if the second residue of $f$ is nonzero its order at the Frobenius image of $v$ is $\ge 0$. Second, for every node pair $s$ of `nodePairsOfPlaces (arithFrobC q k N) W`: if the first residue of $f$ is nonzero and the second vanishes, the order of the first residue at $s_1$ is $> 0$, and symmetrically, if the second residue is nonzero and the first vanishes, the order of the second residue at $s_2$ is $> 0$.
--
--   The statement is the function-field form of the regularity of the two components of the special fibre of $X_0(Nq)$ at $q$, which by Deligne–Rapoport consists of two copies of $X_0(N)$ crossing at the supersingular points; it provides the regularity input used in establishing the Gauss-jump law. It is invoked in the construction of good representatives whose image in the pair of degree-zero divisor class groups is an inertial displacement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_oneSidedRegularityLaw_of_isModel_of_not_dvd.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.oneSidedRegularityLaw_of_isModel_of_not_dvd
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    R.OneSidedRegularityLaw W := by sorry
