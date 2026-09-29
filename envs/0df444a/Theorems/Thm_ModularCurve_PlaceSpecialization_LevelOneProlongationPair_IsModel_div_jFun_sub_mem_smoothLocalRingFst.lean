-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_div_jFun_sub_mem_smoothLocalRingFst
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.div_jFun_sub_mem_smoothLocalRingFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/9e3a00f7-8aaa-5a1d-99d8-729a352c9190
-- title:
--   Division by j-j₀ in the smooth local ring at a type-one point
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} \colon A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, and integrality hypotheses `hα`, `hβ` for the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ and prime $q$. Let $P$ be a place specialisation for these data and let $R$ be a level-one prolongation pair for $P$ satisfying `IsModel`, i.e. the conjunction of the two divisor laws and the two cusp laws at $\infty$ and at $0$. Let $Q$ be a place of $\overline{\mathbb Q}$-modular function field $\overline{\mathcal F}_{1\cdot q}$ that is of strict type one for $P$: Frobenius carries $P.\mathrm{redFst}\,Q$ to $P.\mathrm{redSnd}\,Q$, while its square does not return $P.\mathrm{redFst}\,Q$. Let $j_0 \in A$ be such that $\mathrm{ord}_Q(j - j_0) > 0$, where $j$ is `jFun`, the $j$-function viewed in $\overline{\mathcal F}_{1\cdot q}$ and $j_0$ is mapped in from $\overline{\mathbb Q}$. Finally let $r$ belong to the subring $R.\mathrm{smoothLocalRingFst}(P.\mathrm{redFst}\,Q)$, that is, $r$ lies in the integers of $R.R_1$ and in the valuation ring of every strict-type-one place $W$ with $P.\mathrm{redFst}\,W = P.\mathrm{redFst}\,Q$, and suppose $\mathrm{ord}_Q r > 0$. Then $r/(j - j_0)$ again lies in $R.\mathrm{smoothLocalRingFst}(P.\mathrm{redFst}\,Q)$.
--
--   This is the division step that makes $j - j_0$ behave as a local parameter at a strict type-one point: an element of the local ring of the model at the corresponding smooth point which vanishes at $Q$ itself is divisible, within that local ring, by $j - j_0$. It feeds the construction of $t$-expansions of elements of that local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_div_jFun_sub_mem_smoothLocalRingFst.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.div_jFun_sub_mem_smoothLocalRingFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hQ : P.IsStrictTypeOne Q)
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)))
    (r : ↥(modularFunctionFieldBar (1 * q))) (hr : r ∈ R.smoothLocalRingFst (P.redFst Q))
    (hrQ : 0 < Q.ord r) :
    r / (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ∈
      R.smoothLocalRingFst (P.redFst Q) := by sorry
