-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_tPoleOrderLE_of_qExpand
-- name    : ModularCurve.PhiGen.tPoleOrderLE_of_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/68ace00f-4348-5344-a199-4252ac06538e
-- title:
--   Pole order descends along t ↦ t^N
-- statement:
--   Let $K$ be a field, let $f$ be a Laurent series over $K$ (an element of `LaurentSeries K`, i.e. a Hahn series over $K$ with value group $\mathbb{Z}$), and let $N, n$ be natural numbers with $N$ nonzero. Write `qExpand K N` for the ring homomorphism on `LaurentSeries K` obtained by transporting the index set along the injective, strictly order-preserving map $m \mapsto N m$ of $\mathbb{Z}$; concretely it sends a series to the series whose coefficient at $Nm$ is the coefficient of the original at $m$ and whose coefficients at indices not divisible by $N$ vanish, that is, it substitutes $t^{N}$ for $t$. The predicate `TPoleOrderLE g k` asserts that the coefficient of $g$ at $m$ vanishes for every integer $m < -k$. The hypothesis is `TPoleOrderLE (qExpand K N f) (N * n)`: all coefficients of $f(t^{N})$ at indices strictly below $-Nn$ vanish. The conclusion is `TPoleOrderLE f n`: all coefficients of $f$ at indices strictly below $-n$ vanish, i.e. $f$ has a pole of order at most $n$ at $t = 0$.
--
--   This records that the bound on the order of the pole of a Laurent series at the cusp can be read off after the substitution $q \mapsto q^{N}$, the pole order being scaled by $N$. It is used in bounding the weighted support of the coefficients of a `ModularPolynomialData`, via [`ModularCurve.ModularPolynomialData.weighted_support_le`](thm.html#ModularCurve.ModularPolynomialData.weighted_support_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_tPoleOrderLE_of_qExpand.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.tPoleOrderLE_of_qExpand {K : Type*} [Field K] {f : LaurentSeries K} {N n : ℕ} [NeZero N] (h : TPoleOrderLE (qExpand K N f) (N * n)) : TPoleOrderLE f n := by sorry
