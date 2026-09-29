-- Prove2me | Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidalSnd
-- name    : ModularCurve.not_isStrictType_of_isCuspidalSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/9afb488e-6c03-565c-a5d3-cf196c11c752
-- title:
--   Cuspidality on the j_q-side excludes strict type
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and let `hα`, `hβ` assert that the two level-raising maps `heckeAlphaBar`, `heckeBetaBar` from the level-$1$ to the level-$q$ function field over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data at level $N = 1$, which specialises places and degree-zero divisor classes of the level-one modular function field over $\overline{\mathbb Q}$ to those over $k$ compatibly with $j$ and its $q$-twist, and let $W$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$. Assume `P.IsCuspidal' W`, i.e. $\operatorname{ord}_W(j_q - a) \le 0$ for every $a \in A$ (no $A$-integral value of $j_q$ at $W$). Then $W$ satisfies neither `P.IsStrictTypeOne` nor `P.IsStrictTypeTwo`: in each case the clause demanding that the relevant reduction `P.redFst W`, resp. `P.redSnd W`, be moved by the square of `frobOnPlacesGeomLevel` fails.
--
--   This is the $j_q$-side (Fricke-transformed) companion of the statement that points of $X_0(q)_{\overline{\mathbb Q}}$ lying above a cusp have no strict type: cuspidal points reduce to the place at infinity on both geometric components, which is Frobenius-fixed, so the two Frobenius-mobility conditions defining the strict types cannot hold. It is used in the analysis of the level-one prolongation pairs, in particular to locate the cusp $\bar{0}$ off the chart at infinity and to control orders of residues at the first component away from that cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_isStrictType_of_isCuspidalSnd.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.not_isStrictType_of_isCuspidalSnd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal' W) :
    ¬ P.IsStrictTypeOne W ∧ ¬ P.IsStrictTypeTwo W := by sorry
