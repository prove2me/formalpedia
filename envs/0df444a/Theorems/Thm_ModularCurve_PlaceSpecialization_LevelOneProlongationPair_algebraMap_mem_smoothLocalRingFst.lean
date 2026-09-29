-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_algebraMap_mem_smoothLocalRingFst
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_mem_smoothLocalRingFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/d0006bf1-e78b-5897-a685-34aba119ecf7
-- title:
--   Constants from A lie in `smoothLocalRingFst`
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`), a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix furthermore modular polynomial data `data` for $q$ — a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ — together with a proof `hKr` that its reduction modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the bivariate sense used by `KroneckerCongruence`, and proofs `hα`, `hβ` that the two Hecke correspondence maps `heckeAlphaBar` and `heckeBetaBar` at level $1$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data and $R$ a level-one prolongation pair for $P$; let $v$ be a place of the function field $k(j, j_q)$ over $k$, that is of `modularFunctionFieldC k 1`, and let $a \in A$. The assertion is that the image of $a$ under the structure map $\overline{\mathbb{Q}} \to$ `modularFunctionFieldBar (1 * q)` lies in the subring `R.smoothLocalRingFst v`, i.e. in the intersection of the valuation subring `R.R₁.integers` with the valuation subrings of all places $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb{Q}}$ satisfying `P.IsStrictTypeOne W` and `P.redFst W = v`.
--
--   This is the statement that the constants coming from $A$ are contained in the local ring at a smooth point $v$ of the first component of the model of $X_0(q)$, as that local ring is defined by `smoothLocalRingFst`. It serves as a bookkeeping input for the $t$-expansion results about models, being cited by `IsModel.exists_ringHom_tExpansion`, `IsModel.exists_tExpansion_of_mem_smoothLocalRingFst` and `IsModel.neg_one_le_ord_residue_of_eq_one_add_mul`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_algebraMap_mem_smoothLocalRingFst.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_mem_smoothLocalRingFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (v : Place k ↥(modularFunctionFieldC k 1)) (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.smoothLocalRingFst v := by sorry
