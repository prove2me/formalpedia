-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_hasseExp_eq_zero_of_t_eq_one
-- name    : ModularCurve.MultCovering.hasseExp_eq_zero_of_t_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/eaa73021-489d-5adb-97f0-5a75c1dc8566
-- title:
--   Hasse exponent vanishes for a member equal to 1
-- statement:
--   Let $p$ be a prime, let $r$ be a natural number, and let $\Phi$ be family data of level $p$ with $r$ members, i.e. a term of `FamData p r`: a family $t : \mathrm{Fin}\,r \to \overline{F}_{1\cdot p}$ of elements of `modularFunctionFieldBar (1 * p)`, the base change to $\overline{\mathbb{Q}}$ of the intermediate field $F_{1\cdot p} = \mathbb{Q}(\mathrm{divisorExpansions}(1\cdot p))$ of $\mathbb{Q}((q))$ inside $\overline{\mathbb{Q}}((q))$, together with a family $tRat$ of elements of $F_{1\cdot p}$ itself and the requirement that each $t\,l$ be the image of $tRat\,l$ under the coefficientwise embedding `coeffEmb` of $\mathbb{Q}((q))$ into $\overline{\mathbb{Q}}((q))$. Let $l$ be an index with $\Phi.t\,l = 1$. The conclusion is that `hasseExp Φ l` $= 0$: that is, the natural number obtained by truncating the integer `hasseContent Φ l` — a least $p$-adic valuation among the nonzero coefficients of the rational Laurent series `zeroSeries Φ l`, when such a least value exists, and $0$ otherwise — is zero; equivalently `hasseContent Φ l` $\le 0$.
--
--   This is the family-data form of the statement that a member of the family which is identically $1$ has vanishing valuation exponent at the zero cusp, the normalising case $n_l = 0$ of the content bookkeeping for the members' expansions. It is used by [`ModularCurve.MultCovering.FamData.t_zeroChart_of_orth`](thm.html#ModularCurve.MultCovering.FamData.t_zeroChart_of_orth) and in the construction of unimodular family data with wide certificates at level $11$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_hasseExp_eq_zero_of_t_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.hasseExp_eq_zero_of_t_eq_one {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) (h : Φ.t l = 1) : hasseExp Φ l = 0 := by sorry
