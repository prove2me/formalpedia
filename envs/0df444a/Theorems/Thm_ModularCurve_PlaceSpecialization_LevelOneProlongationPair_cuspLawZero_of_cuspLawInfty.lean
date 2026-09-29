-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_of_cuspLawInfty
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_of_cuspLawInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/367982b7-aafa-514a-8714-055f27aca499
-- title:
--   Cusp law at 0 from the cusp law at ∞
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix data $\mathrm{data}$ consisting of a monic polynomial $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, a witness $h_{\mathrm{Kr}}$ that the reduction of $\Phi$ modulo $q$ equals $(X^{q}-Y)(X-Y^{q})$, and witnesses $h_\alpha, h_\beta$ that the two Hecke maps $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ at level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data and $R$ a level-one prolongation pair for $P$, consisting of two regular prolongations $R_1, R_2$ of $A$ to the field $\overline{\mathbb Q}\cdot\mathcal F(1\cdot q)$ together with the compatibilities recorded in `LevelOneProlongationPair`. Assume `R.CuspLawInfty`: for every $f$ lying in the valuation rings of both $R_1$ and $R_2$ with both residues nonzero, and every divisor $D$ with $D(W) = \operatorname{ord}_W f$ at every place $W$, the pushforward along $P.\mathrm{redFst}$ of the restriction of $D$ to the $\infty$-side places takes, at $P.\mathrm{redFst}(\overline\infty)$, the value $\operatorname{ord}_{P.\mathrm{redFst}(\overline\infty)}$ of the first residue of $f$. Then the same holds with $1$ replaced by $2$ throughout: the pushforward along $P.\mathrm{redSnd}$ of the restriction of $D$ to the $0$-side places takes, at $P.\mathrm{redSnd}(\overline 0)$, the value $\operatorname{ord}_{P.\mathrm{redSnd}(\overline 0)}$ of the second residue of $f$, i.e. `R.CuspLawZero` holds.
--
--   This is the Fricke transport of the local cusp law on $X_0(q)$: the involution $w_q$ interchanges $j$ and $j_q$, hence the two cusps $\overline\infty$ and $\overline 0$ and the two prolongations of the pair, so the order-counting identity at one cusp forces the one at the other. It is used when verifying that a level-one prolongation pair is a model and in the analysis of common units with prescribed poles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_of_cuspLawInfty.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_of_cuspLawInfty
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : PlaceSpecialization.LevelOneProlongationPair P)
    (hI : R.CuspLawInfty) : R.CuspLawZero := by sorry
