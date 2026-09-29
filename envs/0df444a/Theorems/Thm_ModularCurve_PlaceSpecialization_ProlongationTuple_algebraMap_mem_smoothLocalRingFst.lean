-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_algebraMap_mem_smoothLocalRingFst
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.algebraMap_mem_smoothLocalRingFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/1beec0ba-9786-517e-885f-f246aaae45b0
-- title:
--   Constants from A lie in the first smooth local ring
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $N \ge 1$, let $k$ be a field of characteristic $q$ and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Fix `data`, a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$, a proof `hKr` that its reduction modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the bivariate form recorded by `KroneckerCongruence`, and proofs `hα`, `hβ` that the ring homomorphisms underlying `heckeAlphaBar` and `heckeBetaBar` for $(\overline{\mathbb{Q}}, N, q)$ are integral. Let $P$ be a place specialisation for these data and let $R$ be a prolongation tuple over $P$, so in particular $R$ carries a regular prolongation $R_1$ of $A$ to the field $F =$ `modularFunctionFieldBar (N * q)`. Then for every place $v$ of `modularFunctionFieldC k N` over $k$ and every $a \in A$, the image of $a$ under the structure map $\overline{\mathbb{Q}} \to F$ lies in `R.smoothLocalRingFst v`, that is, it lies in the valuation subring $R_1.\mathrm{integers}$ and in the valuation subring of every place $W$ of $F$ over $\overline{\mathbb{Q}}$ with `P.IsStrictFst W` and `P.reduceFst W = v`.
--
--   This records that scalars from $A$ are available inside the local ring of the first copy of the model at a point of the fibre, so that constants may be moved in and out of it. It is used in the expansion arguments at a smooth point of the reduction, namely in the construction of $t$-expansions at places where the residue has order one and in the bound on the order of a first residue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_algebraMap_mem_smoothLocalRingFst.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.algebraMap_mem_smoothLocalRingFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : P.ProlongationTuple)
    (v : Place k ↥(modularFunctionFieldC k N)) (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.smoothLocalRingFst v := by sorry
