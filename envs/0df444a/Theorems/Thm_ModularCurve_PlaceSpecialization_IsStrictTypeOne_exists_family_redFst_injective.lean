-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective
-- name    : ModularCurve.PlaceSpecialization.IsStrictTypeOne.exists_family_redFst_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b3531b27-df8e-5704-bbf1-760861c899bb
-- title:
--   Infinitely many strict type one places with distinct first reductions
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $k$ an algebraically closed field of characteristic $q$, and $\mathrm{red}\colon A\to k$ a ring homomorphism. Let `data` be a `ModularPolynomialData q`, that is a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions $(j, j_q)$, and let `hKr` be the Kronecker congruence asserting that $\Phi$ reduced modulo $q$ equals $(C X^{q}-X)(C X-X^{q})$; let `hα` and `hβ` assert that the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` from level $1$ to level $1\cdot q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization A q 1 data hKr k red hα hβ`, the structure consisting of a map $\mathrm{sp}$ from places of `modularFunctionFieldBar 1` to places of `modularFunctionFieldC k 1`, a homomorphism on degree-zero divisor class groups, and the listed compatibility axioms. Then for every natural number $d$ there exists a family $Q\colon \mathrm{Fin}(d+1)\to$ places of `modularFunctionFieldBar (1 * q)` such that each $Q_i$ is of strict type one for $P$, i.e. `frobOnPlacesGeomLevel k 1 data hKr` carries $P.\mathrm{redFst}(Q_i)=\mathrm{sp}$ of the restriction of $Q_i$ along `heckeAlphaBar` to $P.\mathrm{redSnd}(Q_i)$ while its square does not fix $P.\mathrm{redFst}(Q_i)$, and such that $i\mapsto P.\mathrm{redFst}(Q_i)$ is injective.
--
--   This is the supply of arbitrarily many points of $X_0(q)$ over $\overline{\mathbb Q}$ whose first reduction at $q$ lands on a point of the $j$-line not fixed by the square of Frobenius, with pairwise distinct first reductions; it is used to produce the generic base divisor on one component of the special fibre. It is cited by [`ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem`](thm.html#ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective.lean

import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_LevelOneComp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.IsStrictTypeOne.exists_family_redFst_injective
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (d : ℕ) :
    ∃ Q : Fin (d + 1) → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      (∀ i, P.IsStrictTypeOne (Q i)) ∧ Function.Injective fun i => P.redFst (Q i) := by sorry
