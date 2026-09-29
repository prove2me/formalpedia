-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero_of_ord_residue_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/34ebe6fc-b86a-55c5-9557-dc90dd029fe4
-- title:
--   Order bound for a first residue from a t-expansion
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a natural number $N \neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two Hecke correspondences at level $N$ and prime $q$ (`hα`, `hβ`), and a place specialisation $P$ for these data. Assume $q \nmid N$, and let $R$ be a prolongation tuple for $P$ which `IsModel`, i.e. satisfies the two divisor laws and the cusp laws at $\infty$ and at $0$. Let $Q$ be a place of $\overline{\mathbb Q}$ in the field `modularFunctionFieldBar (N * q)` which is strict of the first kind for $P$: geometric-level Frobenius carries $P$'s first reduction of $Q$ to its second reduction, and iterating Frobenius twice does not return the first reduction. Write $\bar v =$ `P.reduceFst Q`. Let $t$ be an element of that field lying in the integers of $R.R₁$ whose first residue has $\mathrm{ord}_{\bar v}$ equal to $1$. Let $r$ likewise lie in the integers of $R.R₁$, let $c : \mathbb{N} \to A$, let $m \in \mathbb{N}$, and assume that $\bigl(r - \sum_{i<m} c_i\, t^i\bigr)/t^m$ lies in `R.smoothLocalRingFst` at $\bar v$ — the intersection of the integers of $R.R₁$ with the valuation subrings of all places $W$ that are strict of the first kind for $P$ with first reduction $\bar v$ — and that $red(c_i) = 0$ for all $i < m$. Then either the first residue of $r$ is $0$, or $m \le \mathrm{ord}_{\bar v}$ of that residue.
--
--   This is the coordinate-free form of the statement that reduction commutes with expansion in a disc parameter: if all coefficients of the truncated $t$-expansion of $r$ die under $red$ and the remainder is regular at every strict place above $\bar v$, then the residue of $r$ vanishes to order at least $m$. It rests on the value law for elements of the smooth local ring (`exists_hasValue_of_mem_smoothLocalRingFst`) and feeds the order estimate used when $t$ is taken to be $j - j(Q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero_of_ord_residue_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero_of_ord_residue_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hQ : P.IsStrictFst Q)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers)
    (htv : (P.reduceFst Q).ord (R.residue₁ ⟨t, ht₁⟩) = 1)
    (r : ↥(modularFunctionFieldBar (N * q))) (h₁ : r ∈ R.R₁.integers)
    (c : ℕ → A) (m : ℕ)
    (hc : (r - ∑ i ∈ Finset.range m, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c i : AlgebraicClosure ℚ) * t ^ i) / t ^ m ∈ R.smoothLocalRingFst (P.reduceFst Q))
    (hred : ∀ i < m, red (c i) = 0) :
    R.residue₁ ⟨r, h₁⟩ = 0 ∨ (m : ℤ) ≤ (P.reduceFst Q).ord (R.residue₁ ⟨r, h₁⟩) := by sorry
