-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_frickeInvolutionBar_smul
-- name    : ModularCurve.PlaceSpecialization.redSnd_frickeInvolutionBar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c497b632-f920-5f4f-9e78-017fbd7b3f39
-- title:
--   Fricke translation exchanges the two reductions on X₀(q)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$, satisfying the Kronecker congruence `hKr`, i.e. the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$; let `hα` and `hβ` assert that the two inclusions $\alpha,\beta$ of the geometric base change of the level-$1$ modular function field into that of level $1 \cdot q$ are integral ring maps. Let $P$ be a `PlaceSpecialization` datum for these inputs: in particular it provides a map $\mathrm{sp}$ from places of `modularFunctionFieldBar 1` over $\overline{\mathbb Q}$ to places of `modularFunctionFieldC k 1`, a homomorphism on degree-zero divisor class groups, and compatibility conditions on the orders of $j$-functions. For every place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$, the asserted identity is $P.\mathrm{redSnd}(w_q \cdot W) = P.\mathrm{redFst}(W)$, where $w_q$ is `frickeInvolutionBar (1 * q)` acting on places, $\mathrm{redFst}(W) = \mathrm{sp}(W|_{\alpha})$ and $\mathrm{redSnd}(W) = \mathrm{sp}(W|_{\beta})$.
--
--   This records, at the level of places and after specialisation to characteristic $q$, the classical fact that the Fricke involution $w_q$ interchanges the two degeneracy maps $X_0(q) \to X(1)$, hence the two components of the special fibre at $q$. It is used in the construction of the splitting datum for a level-one prolongation pair, [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.splitDatum_of_forall_centred_ord_eq`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.splitDatum_of_forall_centred_ord_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_redSnd_frickeInvolutionBar_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.redSnd_frickeInvolutionBar_smul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redSnd (frickeInvolutionBar (1 * q) • W) = P.redFst W := by sorry
