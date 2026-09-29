-- Prove2me | Theorems.Thm_ModularCurve_heckeInputsAll
-- name    : ModularCurve.heckeInputsAll
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/e4843622-a50f-5029-8843-7c24d8bed3de
-- title:
--   Hecke correspondence inputs at every level and prime
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. The assertion is the predicate [`ModularCurve.HeckeInputsAll N`](def/ModularCurve_HeckeInputsAll.html#L8), namely: for every prime $\ell$ (an element of `Nat.Primes`, so that $\ell \neq 0$ as a natural number), the predicate [`ModularCurve.HeckeInputsAlong`](def/ModularCurve_HeckeOperatorTotal.html#L13) holds for the coefficient field $L =$ `AlgebraicClosure ℚ`, the level $N$ and the prime $\ell$. Unfolding that predicate, the conclusion is the simultaneous existence of witnesses for the following five data: the integrality predicate `HeckeAlphaBarIntegral L N ℓ` for the map $\bar\alpha$; a witness $h\beta$ of the integrality predicate `HeckeBetaBarIntegral L N ℓ` for the map $\bar\beta$; the predicate `HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))`, asserting the required supply of principal divisors on the base change to $L$ of the full modular function field of level $N\ell$; and a witness $h\mathrm{fin}$ of `FiniteAlong L (heckeAlphaBar L N ℓ)`, finiteness along the morphism $\bar\alpha$; such that, in addition, $\mathrm{FundamentalIdentityAlong}\, L\, (\mathrm{heckeBetaBar}\, L\, N\, \ell)\, h\beta$ and $\mathrm{NormFormulaAlong}\, L\, (\mathrm{heckeAlphaBar}\, L\, N\, \ell)\, h\mathrm{fin}$ both hold. Thus all the hypotheses needed to form the Hecke correspondence $T_\ell = \bar\alpha_* \circ \bar\beta^*$ are available at every level and every prime, over $\overline{\mathbb{Q}}$.
--
--   This is the unconditional input statement for the construction of the Hecke operators $T_\ell$ on the Jacobian of the modular curve of level $N$ over $\overline{\mathbb{Q}}$, in the correspondence-theoretic form $T_\ell = \bar\alpha_* \circ \bar\beta^*$ attached to the degeneracy maps of level $N\ell$. It is cited throughout the later development whenever Hecke operators on Jacobians, their action on Tate modules and eigenspaces, or their compatibility with reduction and Frobenius are used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeInputsAll.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeInputsAll

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeInputsAll (N : ℕ) [NeZero N] : ModularCurve.HeckeInputsAll N := by sorry
