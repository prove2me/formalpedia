-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_ne_integers
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_ne_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/6cd68852-0d44-5c3c-bd81-628aca6e3851
-- title:
--   The two level-one prolongations have distinct valuation rings
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that the image of $q$ is a nonunit of $A$; let $k$ be a field of characteristic $q$ and $red : A \to k$ a ring homomorphism. Let `data` be modular polynomial data for $q$, that is, a monic $\Phi \in (\mathbb{Z}[X])[Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_{q})$, and let `hKr` assert the Kronecker congruence that $\Phi$ reduced modulo $q$ equals $(X^{q}-Y)(X-Y^{q})$; let `hα`, `hβ` assert integrality of the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $1$ and prime $q$ over $\overline{\mathbb{Q}}$. Given a place specialisation datum $P$ for these inputs and a level-one prolongation pair $V$ for $P$ — which packages a lift $\bar{red}$ of $red$ to the residue field of $A$, a comparison map $\iota$ of modular function fields, and two regular prolongations $R_1$, $R_2$ of $A$ to the geometric modular function field of level $1\cdot q$ with residue field the full modular function field of level $1$ over the residue field of $A$, subject to coefficientwise computation of $R_1$-residues, the relation that $f$ lies in $R_2$ exactly when its Fricke image $w_q f$ lies in $R_1$ with matching residues, and compatibility of the $R_1$-residue with reduction via $\iota$ — the conclusion is that the valuation subrings underlying $R_1$ and $R_2$ are not equal.
--
--   This records that the two prolongations furnished by a level-one prolongation pair are genuinely distinct, reflecting the fact that the special fibre of $X_0(q)$ at $q$ has two components rather than one. Distinctness supplies the injectivity hypothesis needed to apply the fundamental inequality [`AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le`](thm.html#AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le) to the pair, and it is used by the two results `integers_eq_or_eq_of_forall_mem_iff_pencil` and `integers_eq_or_eq_of_transcendental`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_ne_integers.lean

import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_ne_integers
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (V : P.LevelOneProlongationPair) :
    V.R₁.integers ≠ V.R₂.integers := by sorry
