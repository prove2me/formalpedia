-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_eq_of_isModel_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.eq_of_isModel_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/cbb9f616-f462-5e0d-a1a9-c4ffdb3123ed
-- title:
--   Uniqueness of specialisation packets carrying a model prolongation tuple
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N\ge 1$, a field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A\to k$, modular polynomial data at $q$ (a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi(j,j_q)=0$) whose bivariate reduction mod $q$ satisfies the Kronecker congruence $(\mathrm{C}\,X^q-X)(\mathrm{C}\,X-X^q)$, and hypotheses $h\alpha,h\beta$ asserting that the Hecke coordinate maps $\overline{\alpha},\overline{\beta}$ at level $N$ and $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms; assume $q\nmid N$. Let $P,P'$ be two place-specialisation packets for these data, each consisting of a map $\mathrm{sp}$ from places of the level-$N$ function field over $\overline{\mathbb{Q}}$ to places of $\mathrm{modularFunctionFieldC}\ k\ N$, a homomorphism $\mathrm{spPic0}\colon \mathrm{JZero}\ N\to \mathrm{Pic}^0$ of the reduced curve, and the packet's compatibility clauses on orders of the coordinates $j$, $j_N$ and their reductions. Suppose $R$ is a prolongation tuple over $P$ — a lift $\overline{\mathrm{red}}$ of $\mathrm{red}$ to the residue field of $A$, the induced coefficientwise embedding $\iota$, and two regular prolongations $R_1,R_2$ of $A$ to the level-$Nq$ field, whose rings of integers are described by the localised modular ring and its Atkin–Lehner translate at $q$ — which satisfies `IsModel`, i.e. the two divisor laws and the cusp laws at the infinity and zero sides, and `OrderLawFixed`: for every $f$ in the level-$Nq$ field lying in the integers of both $R_1$ and $R_2$ with both residues nonzero, every divisor $D$ with $D(W)=\mathrm{ord}_W(f)$ for all $W$, and every affine geometric place $v$ of $\mathrm{modularFunctionFieldC}\ k\ N$ fixed by the square of the geometric-level Frobenius $\varphi$, the pushforward of $D$ along $P.\mathrm{reduceFst}$ at $v$ equals $\mathrm{ord}_v(R_1\text{-residue of }f)+\mathrm{ord}_{\varphi v}(R_2\text{-residue of }f)$. Assume the same for a tuple $R'$ over $P'$. Then $P=P'$.
--
--   This is the rigidity statement for specialisation packets of $X_0(N)$ at a prime $q$ not dividing $N$: the reduction data of a packet is pinned down, at every genus, by the existence of a prolongation tuple at level $Nq$ that is a model and obeys the order law at the places fixed by the square of Frobenius, the two prolongations corresponding to the two components of the special fibre exchanged by the Atkin–Lehner involution. It is used in the construction of glued specialisations and of good divisor classes on the reduced curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_eq_of_isModel_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.eq_of_isModel_of_orderLawFixed
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (R' : PlaceSpecialization.ProlongationTuple P') (hmodel' : R'.IsModel) (hO' : R'.OrderLawFixed) :
    P = P' := by sorry
