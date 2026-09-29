-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/075b81cc-6022-5551-9f26-3b2e3cb40c34
-- title:
--   ∞-side places over a non-integral j-place have ramification sum 1
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$), a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix further data $\mathrm{data}$ consisting of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the $q$-expansion pair, subject to the Kronecker congruence $hKr$, which says that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$; assume the two degeneracy inclusions `heckeAlphaBar` and `heckeBetaBar` of $\overline{\mathbb{Q}}$-base-changed modular function fields from level $N$ to level $Nq$ are integral ($h\alpha$, $h\beta$), that the level-$Nq$ field has principal divisors, and that $q \nmid N$. Let $P$ be a term of `PlaceSpecialization A q N data hKr k red hα hβ`, and let $b$ be a place of the level-$N$ field `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ such that $\mathrm{ord}_b(j - a) \le 0$ for every $a \in A$, where $j$ is the coefficientwise image of the $q$-expansion `jq`. Then, summing over those places $W$ of the level-$Nq$ field lying over $b$ along `heckeAlphaBar` which satisfy `IsInftySide P`, i.e. which satisfy the predicate `IsCuspidal P` and at which the chart function `tInfty N q` takes a value $\tau \in A$ with $\mathrm{red}\,\tau = 1$, the ramification indices of $W$ over $b$ along `heckeAlphaBar`, viewed as integers, add up to $1$.
--
--   This is the local statement that over a place of $X_0(N)$ where $j$ has no value in $A$ — a cusp, or a place in the residue disc of a cusp of the special fibre — exactly one place of $X_0(Nq)$ in the fibre of the first degeneracy map lies on the $\infty$-side, and it is unramified there, the remaining $q$ of the degree $q+1$ being carried by the other side. It is used in the proof of the $\infty$-side cusp law `cuspLawInfty_of_sp_eq_spPlace_of_cuspChart`, which compares the two sheets of $X_0(Nq)$ over $X_0(N)$ at cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve ModularCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : ∀ a : A, b.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1 := by sorry
