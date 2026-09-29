-- Prove2me | Theorems.Thm_HahnSeries_HasRamBound_add
-- name    : HahnSeries.HasRamBound.add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e7778773-cac0-5937-8eb3-dd3153fd3da3
-- title:
--   Ramification bounds are closed under addition
-- statement:
--   Let $K$ be a field, let $e$ be a natural number, and let $x$ and $y$ be Hahn series over $K$ with value group $\mathbb{Q}$, i.e. elements of `HahnSeries ℚ K`. Say that a Hahn series $z$ satisfies `HasRamBound e z` when its support is contained in the range of the map $\mathbb{Z} \to \mathbb{Q}$, $k \mapsto k/e$; that is, every exponent at which $z$ has a non-zero coefficient is of the form $k/e$ for some integer $k$. Assuming `HasRamBound e x` and `HasRamBound e y`, the conclusion is `HasRamBound e (x + y)`: every exponent in the support of $x + y$ is again of the form $k/e$ with $k \in \mathbb{Z}$. No positivity assumption on $e$ is made; for $e = 0$ the range in question is the singleton $\{0\}$ (division by zero in $\mathbb{Q}$ returning $0$), so in that degenerate case the hypotheses and the conclusion say that the series are supported at the exponent $0$ alone.
--
--   This is the additive closure half of the statement that the generalised power series with exponents in $\tfrac1e\mathbb{Z}$ — the Puiseux series in an $e$-th root of the uniformiser — form a subring, indeed a subfield, of `HahnSeries ℚ K`. It is used in the analysis of ramification of $q$-expansions on modular curves, feeding into [`ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound`](thm.html#ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HahnSeries_HasRamBound_add.lean

import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries

theorem HahnSeries.HasRamBound.add {K : Type*} [Field K] {e : ℕ} {x y : HahnSeries ℚ K} (hx : HasRamBound e x)
    (hy : HasRamBound e y) : HasRamBound e (x + y) := by sorry
