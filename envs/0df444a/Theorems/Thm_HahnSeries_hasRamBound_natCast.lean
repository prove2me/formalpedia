-- Prove2me | Theorems.Thm_HahnSeries_hasRamBound_natCast
-- name    : HahnSeries.hasRamBound_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/a679ab7b-591e-562e-a4c3-a848edeb09c3
-- title:
--   Natural numbers have every ramification bound in HahnSeries ℚ K
-- statement:
--   Let $K$ be a field, let $e$ be a natural number and let $n$ be a natural number. Consider the ring $\mathrm{HahnSeries}\ \mathbb{Q}\ K$ of Hahn series with rational exponents and coefficients in $K$, and the image of $n$ in it under the canonical map from $\mathbb{N}$. The assertion is that this element satisfies `HasRamBound e`, which by definition means that its support — the set of rational exponents at which its coefficient is non-zero — is contained in the set of rationals of the form $k/e$ with $k \in \mathbb{Z}$. There are no hypotheses beyond $K$ being a field: in particular $e$ is allowed to be $0$, in which case $k/e$ is $0$ for every $k$ and the admissible exponent set is $\{0\}$, and $n$ is allowed to be $0$, or to have vanishing image in $K$ when $K$ has positive characteristic, in which case the series is $0$ and its support is empty. The statement concerns natural numbers only, although the same holds for integers.
--
--   This records that the prime subring of the Hahn series field sits inside the Puiseux-type subfield of series with denominators dividing $e$; by [`HahnSeries.mem_puiseuxRamSubfield_iff`](thm.html#HahnSeries.mem_puiseuxRamSubfield_iff) the predicate `HasRamBound e` is, for $e>0$, membership in [`HahnSeries.puiseuxRamSubfield K he`](def/HahnSeries_RamificationBound.html#L37). It is used when the modular equation, whose coefficients are rational integers and hence constant series, is evaluated at a series with ramification bound $e$, in [`ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound`](thm.html#ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HahnSeries_hasRamBound_natCast.lean

import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries

theorem HahnSeries.hasRamBound_natCast {K : Type*} [Field K] {e : ℕ} (n : ℕ) : HasRamBound e ((n : HahnSeries ℚ K)) := by sorry
