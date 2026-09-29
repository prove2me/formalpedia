-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/e059cbf3-4f6a-5e7a-be7f-4eebcc45183f
-- title:
--   Order ≥ m for the first residue at a reduced place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ killing the pair $(j,j_q)$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$, integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps at level $1$ and prime $q$, a place specialisation $P$, and a level-one prolongation pair $R$ for $P$ which is a model, i.e. satisfies the two divisor laws and the cusp laws at $\infty$ and at $0$. Let $Q$ be a place of $\overline{\mathbb Q}(X_0(q))$, written `modularFunctionFieldBar (1 * q)`, over $\overline{\mathbb Q}$, which is strictly of type one for $P$: the geometric-level Frobenius carries `P.redFst Q` to `P.redSnd Q`, while its square does not fix `P.redFst Q`. Let $j_0 \in A$ with $\mathrm{ord}_Q(j - j_0) > 0$, where $j$ denotes `PlaceSpecialization.jFun`. Let $r$ lie in the integers of `R.R₁` and in `R.smoothLocalRingFst (P.redFst Q)`, the intersection of those integers with the valuation rings of all strictly type-one places $W$ with `P.redFst W = P.redFst Q`. Let $c \colon \mathbb N \to A$ and $m \in \mathbb N$ be such that $\bigl(r - \sum_{i<m} c_i\,(j - j_0)^i\bigr)/(j-j_0)^m$ again lies in `R.smoothLocalRingFst (P.redFst Q)`, and assume $\mathrm{red}(c_i) = 0$ for all $i < m$. Then the first residue $\bar r =$ `R.residue₁ ⟨r, h₁⟩`, an element of the mod-$q$ level-one function field, either vanishes or satisfies $m \le \mathrm{ord}_{\,\mathrm{redFst}\,Q}(\bar r)$, the order being the integer $-\log$ of the adic valuation.
--
--   This is a vanishing-order transfer statement for the mod-$q$ model of $X_0(q)$ provided by a level-one prolongation pair: if the first $m$ coefficients of the expansion of $r$ in the local parameter $j - j_0$ at a strictly type-one place reduce to zero, then the reduction of $r$ vanishes to order at least $m$ at the reduced place. It is used in the first-order estimates bounding the pole order of a reduced function, through [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.neg_one_le_ord_residue_of_eq_one_add_mul`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.neg_one_le_ord_residue_of_eq_one_add_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hQ : P.IsStrictTypeOne Q)
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)))
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₁ : r ∈ R.R₁.integers)
    (hr : r ∈ R.smoothLocalRingFst (P.redFst Q))
    (c : ℕ → A) (m : ℕ)
    (hc : (r - ∑ i ∈ Finset.range m,
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c i : AlgebraicClosure ℚ) *
            (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ i) /
        (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ m ∈
      R.smoothLocalRingFst (P.redFst Q))
    (hred : ∀ i < m, red (c i) = 0) :
    R.residue₁ ⟨r, h₁⟩ = 0 ∨ (m : ℤ) ≤ (P.redFst Q).ord (R.residue₁ ⟨r, h₁⟩) := by sorry
