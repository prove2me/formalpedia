-- Prove2me | Theorems.Thm_ModularCurve_LevelP_isDomain_and_isIntegrallyClosed_univBase
-- name    : ModularCurve.LevelP.isDomain_and_isIntegrallyClosed_univBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/127bb363-b4cd-549f-94e9-045022ee02c7
-- title:
--   Universal base ring ℤ[aᵢ][1/(pΔ)] is integrally closed domain
-- statement:
--   Let $p$ be a natural number with $p \neq 0$. Work in the polynomial ring $\mathbb{Z}[a_1,a_2,a_3,a_4,a_6]$ in five indeterminates, i.e. `MvPolynomial (Fin 5) ℤ`, carrying the generic Weierstrass curve `genericCurve` whose five coefficients are the indeterminates, and put $p\Delta$ for the element `pDelta p`, the product of the image of $p$ under the canonical map $\mathbb{N} \to \mathbb{Z}[a_1,\dots,a_6]$ with the discriminant $\Delta$ of that curve. The ring [`ModularCurve.LevelP.UnivBase p`](def/ModularCurve_KatzLevelPUniversal.html#L247) is by definition the localisation of $\mathbb{Z}[a_1,\dots,a_6]$ away from $p\Delta$, that is, $\mathbb{Z}[a_1,\dots,a_6][(p\Delta)^{-1}]$, equipped with its canonical commutative ring and $\mathbb{Z}[a_1,\dots,a_6]$-algebra structures and its universal property as an `IsLocalization.Away` at $p\Delta$. The assertion is the conjunction of two statements about this ring: it is an integral domain (nontrivial, with no zero divisors), and it is integrally closed, in the sense that every element of its field of fractions integral over it lies in the image of the ring.
--
--   This records that the universal base for Weierstrass curves with $p$ and the discriminant inverted is a normal integral domain, so that both instances are available at once to later constructions. It is used in the construction of Katz-style forms of level $\Gamma_0$ and in the global Drinfeld-level analysis of sections of Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_isDomain_and_isIntegrallyClosed_univBase.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.LevelP.isDomain_and_isIntegrallyClosed_univBase (p : ℕ) (hp : p ≠ 0) :
    IsDomain (ModularCurve.LevelP.UnivBase p) ∧
      IsIntegrallyClosed (ModularCurve.LevelP.UnivBase p) := by sorry
