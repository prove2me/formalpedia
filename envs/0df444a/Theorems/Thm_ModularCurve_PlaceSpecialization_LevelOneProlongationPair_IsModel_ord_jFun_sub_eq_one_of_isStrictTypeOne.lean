-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.ord_jFun_sub_eq_one_of_isStrictTypeOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/a3450d28-1d7f-50e4-8039-7d162a86c5af
-- title:
--   Simple zero of j-j₀ at a strict-type-one place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions $(j, j_q)$, let `hKr` assert the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$ in the bivariate normalisation used in the project, and let `hα`, `hβ` assert that the two Hecke maps $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ at level $1$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialization of these data, and let $R$ be a level-one prolongation pair for $P$ satisfying `IsModel`, i.e. the conjunction of the two divisor laws `DivisorLawFst`, `DivisorLawSnd` and the two cusp laws `CuspLawInfty`, `CuspLawZero`. Let $Q$ be a place of the field $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$, that is, a proper valuation subring containing the image of $\overline{\mathbb Q}$ whose ring is a principal ideal ring, and suppose $Q$ is of strict type one for $P$: the geometric Frobenius on places at level $1$ carries $P.\mathrm{redFst}\,Q$ to $P.\mathrm{redSnd}\,Q$, while its square does not fix $P.\mathrm{redFst}\,Q$. Let $j_0 \in A$ and write $t = \mathrm{jFun} - j_0$ for the difference of the modular function $j$, viewed in $\mathrm{modularFunctionFieldBar}(1\cdot q)$, and the constant $j_0$. Assume $\mathrm{ord}_Q(t) > 0$. Then $\mathrm{ord}_Q(t) = 1$, and for every place $W$ of the same field that is of strict type one for $P$, satisfies $P.\mathrm{redFst}\,W = P.\mathrm{redFst}\,Q$ and is distinct from $Q$, one has $\mathrm{ord}_W(t) = 0$. Here $\mathrm{ord}$ is the integer-valued order function attached to a place, the negative logarithm of its adic valuation.
--
--   The statement exhibits $t = j - j_0$ as a local uniformiser at a strict-type-one place $Q$ of the level-$q$ modular function field over $\overline{\mathbb Q}$, with no further zero among the strict-type-one places lying in the same residue disc (same first reduction). It is used in the construction of $t$-expansions and in the verification that quotients by $t$ lie in the relevant smooth local rings, which in turn feed the prime-to-$q$ injectivity arguments for the level-one glueing data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.ord_jFun_sub_eq_one_of_isStrictTypeOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hQ : P.IsStrictTypeOne Q)
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ))) :
    Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) = 1 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        P.IsStrictTypeOne W → P.redFst W = P.redFst Q → W ≠ Q →
          W.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) = 0 := by sorry
