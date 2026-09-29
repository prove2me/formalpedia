-- Prove2me | Theorems.Thm_HahnSeries_hasRamBound_single_one
-- name    : HahnSeries.hasRamBound_single_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/825977ce-bce1-565e-a85b-a0770e5dcedd
-- title:
--   The term c t has ramification bound e
-- statement:
--   Let $K$ be a field, let $e$ be a natural number with $0 < e$, and let $c \in K$. Consider the Hahn series over $K$ with value group $\mathbb{Q}$ given by the single term `single (1 : ℚ) c`, that is, the series whose coefficient at the exponent $1$ is $c$ and whose coefficients at all other rational exponents vanish. The assertion is that this series satisfies `HasRamBound e`, which by definition means that its support — the set of rational exponents at which its coefficient is nonzero — is contained in the set $\{k/e : k \in \mathbb{Z}\}$ of rationals with denominator dividing $e$. Concretely, the support is $\{1\}$ when $c \neq 0$ and is empty when $c = 0$, and $1 = e/e$ lies in the stated range; no hypothesis is imposed on $c$. The positivity of $e$ is needed, since for $e = 0$ every quotient $k/e$ equals $0$ and the conclusion would fail for $c \neq 0$.
--
--   This records that the variable $t$, scaled by an arbitrary constant, lies in the ramification-$e$ part of the Hahn series field $\mathbb{Q}$-graded over $K$, i.e. in $K((t^{1/e}))$ for every $e \geq 1$. It is used in the analysis of roots of the modular equation, via [`ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound`](thm.html#ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HahnSeries_hasRamBound_single_one.lean

import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries

theorem HahnSeries.hasRamBound_single_one {K : Type*} [Field K] {e : ℕ} (he : 0 < e) (c : K) :
    HasRamBound e (single (1 : ℚ) c) := by sorry
