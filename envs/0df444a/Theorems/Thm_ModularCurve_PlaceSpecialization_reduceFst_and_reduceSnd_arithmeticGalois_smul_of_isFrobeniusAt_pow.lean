-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
-- name    : ModularCurve.PlaceSpecialization.reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/cbfc2243-520c-58ea-9f0c-723a1238b332
-- title:
--   Frobenius equivariance of both level-N reductions of places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$, a natural number $N \neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix furthermore data $\mathrm{data}$ consisting of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, together with the hypothesis $\mathrm{hKr}$ that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$, and hypotheses $h_\alpha$, $h_\beta$ asserting that the two degeneracy embeddings $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ into the level-$Nq$ one are integral ring maps. Let $P$ be a place specialisation of this data, so in particular $P$ carries a map $P.\mathrm{sp}$ from places of $\mathrm{modularFunctionFieldBar}\,N$ (valuation subrings containing the base field, proper, and principal) to places of $\mathrm{modularFunctionFieldC}\,k\,N$, subject to the clauses of the structure `PlaceSpecialization`. Assume $k$ algebraically closed. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ and $n$ a natural number such that $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{q^{n}}$. Then for every place $V$ of $\mathrm{modularFunctionFieldBar}\,(N q)$, both reductions
--   $P.\mathrm{reduceFst}\,V = P.\mathrm{sp}$ of the restriction of $V$ along $\mathrm{heckeAlphaBar}$ and $P.\mathrm{reduceSnd}\,V = P.\mathrm{sp}$ of the restriction of $V$ along $\mathrm{heckeBetaBar}$ satisfy
--   $P.\mathrm{reduceFst}(\sigma \cdot V) = \mathrm{arithFrobC}(q,k,N)^{n} \cdot P.\mathrm{reduceFst}\,V$ and $P.\mathrm{reduceSnd}(\sigma \cdot V) = \mathrm{arithFrobC}(q,k,N)^{n} \cdot P.\mathrm{reduceSnd}\,V$, where $\sigma$ acts on places of the level-$Nq$ field through the coefficientwise semilinear automorphism $\mathrm{arithmeticGalois}$ and $\mathrm{arithFrobC}(q,k,N)$ is the semilinear automorphism of $\mathrm{modularFunctionFieldC}\,k\,N$ induced by the $q$-power map on coefficients.
--
--   This is the decomposition-group equivariance of the pair of level-$N$ reductions attached to a place specialisation of the modular curve of level $Nq$: a Frobenius element of residue exponent $q^{n}$ transports each reduction by the $n$-th power of the coefficientwise Frobenius. It is used in the analysis of the nodes of the special fibre at $q$ and in the dichotomy for the first reduction over the two components, both of which compare $\mathrm{reduceFst}$ and $\mathrm{reduceSnd}$ under the Galois action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ) (hσ : A.IsFrobeniusAt σ (q ^ n))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = (arithFrobC q k N) ^ n • P.reduceFst V ∧
    P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = (arithFrobC q k N) ^ n • P.reduceSnd V := by sorry
