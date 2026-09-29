-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
-- name    : ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/313cd2d1-bed6-5807-b788-934813775e4b
-- title:
--   Non-affine fibre places lift to both cuspidal sides
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix also modular polynomial data `data` of level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the level-$q$ $q$-expansion pair) satisfying the Kronecker congruence `hKr`, namely that the reduction of $\Phi$ modulo $q$ equals $(C X^{q} - X)(C X - X^{q})$, together with hypotheses `hα`, `hβ` asserting that the two Hecke maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Assume $q \nmid N$, and let $P$ be a place specialisation datum `PlaceSpecialization` for these data, whose component $P.\mathrm{sp}$ sends places of $\mathrm{modularFunctionFieldBar}\,N$ over $\overline{\mathbb{Q}}$ to places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$. Let $v$ be a place of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ which is not affine geometric, i.e. it is not the case that both $\mathrm{jGeomGen}\,k\,N$ and $\mathrm{jNGeomGen}\,k\,N$ lie in the valuation subring of $v$. Then two existence statements hold. First, there is a place $C$ of $\mathrm{modularFunctionFieldBar}\,(N q)$ over $\overline{\mathbb{Q}}$ which is on the infinity side for $P$ — that is, `IsCuspidal P C` holds and there is $\tau \in A$ with $red\,\tau = 1$ such that $C$ takes the value $\tau$ at $\mathrm{tInfty}\,N\,q$ — and such that $P.\mathrm{reduceFst}\,C = v$, where $P.\mathrm{reduceFst}\,C$ is $P.\mathrm{sp}$ applied to the restriction of $C$ along $\mathrm{heckeAlphaBar}$. Second, there is a place $C$ of $\mathrm{modularFunctionFieldBar}\,(N q)$ which is on the zero side for $P$ — `IsCuspidal' P C` holds and there is $\tau \in A$ with $red\,\tau = 1$ such that $C$ takes the value $\tau$ at $\mathrm{tZero}\,N\,q$ — and such that $P.\mathrm{reduceSnd}\,C = v$, where $P.\mathrm{reduceSnd}\,C$ is $P.\mathrm{sp}$ applied to the restriction of $C$ along $\mathrm{heckeBetaBar}$.
--
--   This is the surjectivity statement for the two cuspidal-region reduction maps: every place of the level-$N$ fibre lying outside the affine $(j, j_N)$-locus is hit both by an infinity-side place and by a zero-side place of the level-$Nq$ function field, via the first and the second reduction respectively. It is used in the subsequent analysis of annulus data and of divisors supported on the two components of the special fibre of $X_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace {q : ℕ}
    [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    (∃ C : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        ProlongationTuple.IsInftySide P C ∧ P.reduceFst C = v) ∧
      (∃ C : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        ProlongationTuple.IsZeroSide P C ∧ P.reduceSnd C = v) := by sorry
