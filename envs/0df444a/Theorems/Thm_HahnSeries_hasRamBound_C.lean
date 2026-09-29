-- Prove2me | Theorems.Thm_HahnSeries_hasRamBound_C
-- name    : HahnSeries.hasRamBound_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/9a31f41d-5acd-56ab-abb1-78069b4fa34c
-- title:
--   Constant Hahn series have ramification bound e
-- statement:
--   Let $K$ be a field, let $e$ be a natural number, and let $a \in K$. Write $C a$ for the constant Hahn series in `HahnSeries ℚ K`, that is, the series over the rationals with coefficients in $K$ whose coefficient at the exponent $0$ is $a$ and whose other coefficients vanish. The assertion is `HasRamBound e (C a)`, which by definition says that the support of $C a$ — the set of exponents in $\mathbb{Q}$ at which its coefficient is nonzero — is contained in the image of the map $\mathbb{Z} \to \mathbb{Q}$, $k \mapsto k/e$. There are no further hypotheses: $a$ may be zero, in which case the series is $0$ and its support is empty, and $e$ may be zero, in which case the set $\{k/e : k \in \mathbb{Z}\}$ reduces to $\{0\}$ under the convention that division by zero yields zero, so the conclusion still holds. Thus constants satisfy the ramification bound $e$ for every $e$ simultaneously.
--
--   This is the statement that the constants of $K$ lie in the subfield of series with exponents in $\tfrac{1}{e}\mathbb{Z}$, the first of the closure properties of the Puiseux-type subfield of `HahnSeries ℚ K` cut out by a ramification bound. It is used when polynomials with constant coefficients are evaluated at series of bounded ramification, and in particular in [`ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound`](thm.html#ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HahnSeries_hasRamBound_C.lean

import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries

theorem HahnSeries.hasRamBound_C {K : Type*} [Field K] {e : ℕ} (a : K) : HasRamBound e (C a : HahnSeries ℚ K) := by sorry
