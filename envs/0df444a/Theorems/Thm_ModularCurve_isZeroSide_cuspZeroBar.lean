-- Prove2me | Theorems.Thm_ModularCurve_isZeroSide_cuspZeroBar
-- name    : ModularCurve.isZeroSide_cuspZeroBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/db1184cb-4e54-5b4e-928a-3748bb63acc2
-- title:
--   The cusp ̄ 0 = w_q∞̄ lies on the zero side
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$ (realised as `AlgebraicClosure ℚ`), a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be modular polynomial data at level $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_{q})$ of $\mathfrak q$-expansions, and let `hKr` be the Kronecker congruence for it: the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$. Let `hα` and `hβ` assert that the two Hecke maps `heckeAlphaBar` and `heckeBetaBar` from the level-$1$ to the level-$q$ Laurent base change over $\overline{\mathbb Q}$ are integral ring homomorphisms. Given a place specialisation $P$ of type `PlaceSpecialization A q 1 data hKr k red hα hβ`, the conclusion is that the place `cuspZeroBar (1 * q)` of $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{q}$, namely the image of the $\mathfrak q$-adic cusp `cuspInftyBar (1 * q)` under the action of the Fricke involution `frickeInvolutionBar`, satisfies `P.IsZeroSide`: the predicate `IsCuspidal'` holds for $P$ at this place, and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that the function $t_0$ (`tZero`) lies in the valuation subring of the place with residue the image of $\tau$.
--
--   This identifies on which of the two components of the Deligne–Rapoport reduction of $X_0(q)$ at $q$ the cusp $\bar 0 = w_q\bar\infty$ lies, in the form used by the project's zero/infinity-side dichotomy for level-one place specialisations. It is used in the analysis of prolongation pairs and of the charts at the two cusps, for instance in the statements that $\bar 0$ avoids the domain of the chart at infinity and in the comparison of the two sheets' rings of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isZeroSide_cuspZeroBar.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.isZeroSide_cuspZeroBar {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : P.IsZeroSide (cuspZeroBar (1 * q)) := by sorry
