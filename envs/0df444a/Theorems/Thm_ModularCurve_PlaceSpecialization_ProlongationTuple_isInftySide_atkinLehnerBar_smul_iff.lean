-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/97c72e8f-654e-5e22-b19e-beb451564f7c
-- title:
--   Atkin–Lehner involution exchanges the ∞- and 0-sides
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix further modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j_q)$), a hypothesis `hKr` that the reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$, and hypotheses $h_\alpha$, $h_\beta$ that the two degeneracy legs `heckeAlphaBar` and `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation of this data, let $q \nmid N$, and let $W$ be a place of the level-$Nq$ modular function field $\overline{\mathbb Q}$-base-changed from $\mathbb Q$, i.e. a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring. Write $w_q$ for `atkinLehnerBar N q`, the geometric base change to $\overline{\mathbb Q}$ of the Atkin–Lehner involution `atkinLehnerInvolutionFull N q` of the level-$Nq$ field, acting on places by the pointwise action. The assertion is that $w_q \cdot W$ satisfies `IsInftySide P` — that is, `IsCuspidal P` holds for $w_q \cdot W$ and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that the function `tInfty N q` lies in the valuation subring of $w_q \cdot W$ with residue the image of $\tau$ — if and only if $W$ satisfies `IsZeroSide P`, namely `IsCuspidal' P` holds for $W$ and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ and $W$ takes the value $\tau$ at `tZero N q`.
--
--   This records the effect of the partial Atkin–Lehner involution $w_q$ at $q \nmid N$ on the two branches of the cuspidal region of $X_0(Nq)$ in characteristic $q$: it interchanges the $\infty$-chart and the $0$-chart conditions, so that statements proved for one side transfer to the other. It is used in the analysis of the two charts of the multiplicative covering and in the cusp law for places lying on the $\infty$-side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    ProlongationTuple.IsInftySide P (ProlongationTuple.atkinLehnerBar N q • W) ↔
      ProlongationTuple.IsZeroSide P W := by sorry
