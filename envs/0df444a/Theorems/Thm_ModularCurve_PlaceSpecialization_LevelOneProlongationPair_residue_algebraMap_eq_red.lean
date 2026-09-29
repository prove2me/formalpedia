-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_algebraMap_eq_red
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_algebraMap_eq_red
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/d10b671f-dd27-553b-8b3f-c06c45971721
-- title:
--   Constants reduce correctly under the first residue map
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$. Let `data` be a `ModularPolynomialData q`, that is a monic $\Phi \in \mathbb Z[x][y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` be the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(x^{q}-y)(x-y^{q})$, and let `hα`, `hβ` assert that the ring homomorphisms underlying `heckeAlphaBar` and `heckeBetaBar` for level $1$ and prime $q$ over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialization datum `PlaceSpecialization A q 1 data hKr k red hα hβ` and let $R$ be a level-one prolongation pair for $P$: it carries a homomorphism $\overline{\mathrm{red}} \colon \mathrm{ResidueField}\,A \to k$ with $\overline{\mathrm{red}} \circ \mathrm{residue}_A = \mathrm{red}$, a coefficientwise embedding $\iota$ of `modularFunctionFieldFullC (ResidueField A) 1` into `modularFunctionFieldC k 1` induced by $\overline{\mathrm{red}}$, and two regular prolongations $R_1$, $R_2$ of $A$ to `modularFunctionFieldBar (1 * q)` with residue field `modularFunctionFieldFullC (ResidueField A) 1`, subject to the stated compatibilities. Then for every $a \in A$ whose image in `modularFunctionFieldBar (1 * q)` lies in `R.R₁.integers`, the value of the residue map `R.residue₁` at that element is the constant $\mathrm{red}\,a$, i.e. the image of $\mathrm{red}\,a$ under the structure map $k \to$ `modularFunctionFieldC k 1`.
--
--   This records that the residue map of the first prolongation, followed by the comparison of residue fields, is compatible with constants: scalars from $A$ reduce to their images under $\mathrm{red}$ inside $k(\tilde\jmath)$. It is used in the analysis of models for the level-one prolongation pair, in particular when vanishing of $\mathrm{red}\,a$ is turned into vanishing of a residue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_algebraMap_eq_red.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_algebraMap_eq_red
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ = algebraMap k ↥(modularFunctionFieldC k 1) (red a) := by sorry
