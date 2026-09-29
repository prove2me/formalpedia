-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b49c5979-f411-5a01-b052-212491c578fe
-- title:
--   Order law at Frobenius-fixed places for prolongation pairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} : A \to k$. Fix further a datum `data` consisting of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, a proof `hKr` that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the two variables, and proofs `hα`, `hβ` that the two Hecke inclusions `heckeAlphaBar`, `heckeBetaBar` of the level-$1$, prime-$q$ situation over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation of this data and $R$ any level-one prolongation pair for $P$, consisting of two regular prolongations $R_1, R_2$ of $A$ to the geometric function field $\overline{\mathbb Q}(X_0(1\cdot q))$ with residue field the level-one function field over the residue field of $A$, together with the comparison maps pinning $R_1$ to reduction of Laurent coefficients, identifying $R_2$ with the $R_1$-pullback along the Fricke involution, and matching $R_1$ with the characteristic-$q$ localised reduction homomorphism. The assertion is the predicate `OrderLawFixed` for $R$: for every $f$ in $\overline{\mathbb Q}(X_0(1\cdot q))$ lying in the valuation rings of both $R_1$ and $R_2$ and with both residues nonzero, every finitely supported divisor $D$ whose value at each place $W$ is $\operatorname{ord}_W f$, and every place $v$ of the level-one function field over $k$ which is fixed by the square of the geometric Frobenius `frobOnPlacesGeomLevel` attached to `data` and `hKr` and which is not the image under `P.redFst` of the cusp place `cuspInftyBar (1*q)`, the pushforward $(\mathrm{Finsupp.mapDomain}\ P.\mathrm{redFst}\ D)(v)$, i.e. the sum of $\operatorname{ord}_W f$ over the places $W$ above $v$, equals $\operatorname{ord}_v$ of the element `R.residue₁ ⟨f, h₁⟩` plus $\operatorname{ord}$ at the Frobenius image of $v$ of the element `R.residue₂ ⟨f, h₂⟩`.
--
--   This is the order (branch-divisor) law at the finite places fixed by the square of the geometric Frobenius, for the two-sheeted reduction of $X_0(q)$ modulo $q$ predicted by the Kronecker congruence: the order of a common unit $f$ summed over the places above $v$ splits as a contribution from the first sheet at $v$ and one from the second sheet at $\varphi(v)$. It is used in the subsequent analysis of the two charts and of common units with prescribed poles on the reduction of $X_0(q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_orderLawFixed.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.orderLawFixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) :
    R.OrderLawFixed := by sorry
