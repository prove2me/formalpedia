-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_tExpansion_of_mem_smoothLocalRingFst
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.exists_tExpansion_of_mem_smoothLocalRingFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/fa6204ee-b1b2-5c39-bcc6-38ab0bd22ec3
-- title:
--   A-integral t-expansion at a smooth point of the level-q model
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` and integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps at level $1$ and prime $q$. Let $P$ be a `PlaceSpecialization` for these data, and let $R$ be a level-one prolongation pair for $P$ satisfying `IsModel`, i.e. the conjunction of the two divisor laws and the two cusp laws. Let $Q$ be a place of $\overline{\mathbb Q}$ in the field $\mathrm{modularFunctionFieldBar}(1\cdot q)$ which is of strict type one for $P$ (Frobenius on geometric-level places carries $P.\mathrm{redFst}\,Q$ to $P.\mathrm{redSnd}\,Q$, while its square does not fix $P.\mathrm{redFst}\,Q$), and let $j_0 \in A$ be such that the element $t := \mathrm{jFun} - j_0$ has strictly positive order at $Q$. Then for every $r$ lying in `R.smoothLocalRingFst (P.redFst Q)` — the subring of elements of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ that belong to the integers of $R.R_1$ and to the valuation subring of every strict-type-one place $W$ with $P.\mathrm{redFst}\,W = P.\mathrm{redFst}\,Q$ — there exists a sequence $c : \mathbb N \to A$ such that for every $m \in \mathbb N$ the quotient $\bigl(r - \sum_{i<m} c_i t^i\bigr)/t^m$ again lies in `R.smoothLocalRingFst (P.redFst Q)`.
--
--   This is the existence of a Taylor expansion, with coefficients in $A$ and with all remainders again integral at the relevant places, of a function regular at a smooth point of the level-$q$ model, taken with respect to the parameter $t = j - j_0$. Formulated as a single membership statement, it simultaneously records the $A$-integrality of the coefficients and the estimate $\mathrm{ord}_Q\bigl(r - \sum_{i<m}c_i t^i\bigr) \ge m$; it is the input to [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.exists_ringHom_tExpansion`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.exists_ringHom_tExpansion), which assembles these expansions into a homomorphism into a power series ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_tExpansion_of_mem_smoothLocalRingFst.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.exists_tExpansion_of_mem_smoothLocalRingFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hQ : P.IsStrictTypeOne Q)
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)))
    (r : ↥(modularFunctionFieldBar (1 * q))) (hr : r ∈ R.smoothLocalRingFst (P.redFst Q)) :
    ∃ c : ℕ → A, ∀ m : ℕ,
      (r - ∑ i ∈ Finset.range m,
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c i : AlgebraicClosure ℚ) *
            (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ i) /
        (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ m ∈
      R.smoothLocalRingFst (P.redFst Q) := by sorry
