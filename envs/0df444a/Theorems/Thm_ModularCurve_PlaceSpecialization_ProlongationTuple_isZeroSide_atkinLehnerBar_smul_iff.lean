-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isZeroSide_atkinLehnerBar_smul_iff
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.isZeroSide_atkinLehnerBar_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/5a1fa02c-149b-5d99-9d1b-80c4a132df7b
-- title:
--   Atkin–Lehner at q swaps the zero and infinity sides
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N \neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix further modular polynomial data at $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with a proof `hKr` that its bivariate reduction mod $q$ equals $(X^q - Y)(X - Y^q)$, and proofs $h\alpha$, $h\beta$ that the two degeneracy legs `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation of these data, let $q \nmid N$, and let $W$ be a place of the level-$Nq$ modular function field $\overline{\mathbb Q} \cdot \mathbb Q(X_{\mathrm{full}}(Nq))$ over $\overline{\mathbb Q}$, i.e. a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring. Then the place $w_q \cdot W$ obtained by transporting $W$ along the base-changed Atkin–Lehner involution `ProlongationTuple.atkinLehnerBar N q` (the geometric automorphism induced by `atkinLehnerInvolutionFull N q`) satisfies `IsZeroSide P`, that is, the predicate `ProlongationTuple.IsCuspidal' P` holds for it and there is $\tau \in A$ with $red\,\tau = 1$ at which it takes the value of the function `tZero N q`, if and only if $W$ satisfies `IsInftySide P`, that is, `ProlongationTuple.IsCuspidal P` holds for $W$ and there is $\tau \in A$ with $red\,\tau = 1$ such that $W$ takes the value $\tau$ at `tInfty N q`; here taking the value $\tau$ means that the function lies in the valuation subring of the place and its residue is the image of $\tau$ in the residue field.
--
--   This is the statement that the partial Atkin–Lehner involution $w_q$ at a prime $q \nmid N$ interchanges the two components of the cuspidal region of the fibre at $q$ of $X_0(Nq)$, the $\infty$-side being carried onto the $0$-side. It is used in the analysis of the two charts covering the special fibre and in the construction of divisors supported on one side, for instance in [`ModularCurve.MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom`](thm.html#ModularCurve.MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom) and [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isZeroSide_atkinLehnerBar_smul_iff.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.isZeroSide_atkinLehnerBar_smul_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    ProlongationTuple.IsZeroSide P (ProlongationTuple.atkinLehnerBar N q • W) ↔
      ProlongationTuple.IsInftySide P W := by sorry
