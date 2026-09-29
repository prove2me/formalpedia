-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
-- name    : ModularCurve.MultCovering.eq_mAnnuli_add_one_of_isEmbBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/7212a79d-d398-5cbd-a371-208512f9c7c4
-- title:
--   Embedding bases on X₀(p) have m(p)+1 members
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $r$ be a natural number, and let $s : \mathrm{Fin}\,r \to \overline{F}$ be a family of elements of $\overline{F} =$ `modularFunctionFieldBar (1 * p)`, the subfield of the Laurent series field over $\overline{\mathbb Q}$ obtained by base change (adjoining the image of the coefficientwise embedding) from the field `modularFunctionFieldFull (1 * p)` of modular functions of level $1 \cdot p$ inside $\mathbb{Q}$-Laurent series. Assume `IsEmbBasis (1 * p) s`, i.e. that $s$ is linearly independent over $\overline{\mathbb Q}$ and that the $\overline{\mathbb Q}$-span of the range of $s$ is exactly the Riemann–Roch space of the divisor `embDivisor (1 * p)` $= \mathrm{embDegree}(1 \cdot p) \cdot \overline{\infty}$, the integer multiple of the cusp $\overline\infty$ by the quantity `embDegree (1 * p)`; here the Riemann–Roch space of a divisor $D$ consists of those $f$ with $v(f) \le \exp(D(v))$ at every place $v$ of $\overline{F}$ over $\overline{\mathbb Q}$. The conclusion is that $r = \mathrm{mAnnuli}\,p + 1$, where $\mathrm{mAnnuli}\,p = \lfloor p/12 \rfloor + [\,p \equiv 2 \bmod 3\,] + [\,p \equiv 3 \bmod 4\,]$.
--
--   The statement fixes the cardinality of any basis of the distinguished Riemann–Roch space on $X_0(p)$ in the combinatorial form $\mathrm{mAnnuli}\,p + 1$, i.e. one member per supersingular annulus of the multiplicative covering of $X_0(p)$ at $p$ plus one; equivalently it records that the number of supersingular $j$-invariants in characteristic $p$ is one more than the genus of $X_0(p)$, and that the space in question has dimension genus $+\,2$. It is used by the lemmas that set up and compare the charts and families attached to those annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.MultCovering
open AlgebraicCurve

theorem ModularCurve.MultCovering.eq_mAnnuli_add_one_of_isEmbBasis (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) : r = mAnnuli p + 1 := by sorry
