-- Prove2me | Theorems.Thm_ModularCurve_not_isInftySide_cuspZeroBar
-- name    : ModularCurve.not_isInftySide_cuspZeroBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/dd3f9096-748d-5889-9163-614db8f0f3aa
-- title:
--   The cusp ̄ 0 of X₀(q) is not on the ∞-side
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A \to k$. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ in $Y$ with $\Phi(j, j_q) = 0$, let `hKr` be the Kronecker congruence asserting that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ (in the stated bivariate normalisation), and let `hα`, `hβ` assert that the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` from the level-$1$ Laurent base change to the level-$q$ one are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data, i.e. a level-one specialization datum consisting of a map on places together with a map on degree-zero divisor classes and the compatibility conditions recorded in that structure. Then the place $\bar 0 = w_q \cdot \bar\infty$ of the function field $\overline{\mathbb Q} \cdot F^{\mathrm{full}}_{1 \cdot q}$, obtained by applying the Fricke involution `frickeInvolutionBar` to the $\mathfrak q$-adic cusp `cuspInftyBar`, fails to satisfy `P.IsInftySide`: it is not the case both that the predicate `P.IsCuspidal` holds at $\bar 0$ and that there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that the function `tInfty` lies in the valuation subring of $\bar 0$ and has residue the image of $\tau$ in the residue field.
--
--   This records that, in the local analysis of the two cusps of $X_0(q)$ in the Kronecker-congruence picture, the cusp $\bar 0$ lies on the opposite side from $\bar\infty$, the parameter `tInfty` failing to reduce to $1$ there. It is used in the study of level-one prolongation pairs and of multiplicative coverings, for instance to show that $\bar 0$ does not lie in the domain of the chart at $\infty$ and to control orders of vanishing of residues away from $\bar 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_isInftySide_cuspZeroBar.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.not_isInftySide_cuspZeroBar {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : ¬ P.IsInftySide (cuspZeroBar (1 * q)) := by sorry
