-- Prove2me | Theorems.Thm_MvPowerSeries_exists_rename_swap_eq_add_mul_X
-- name    : MvPowerSeries.exists_rename_swap_eq_add_mul_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/329cda4c-52a6-5400-bfac-a2700387934f
-- title:
--   Every two-variable power series is A + Bu with A,B symmetric
-- statement:
--   Let $W$ be a commutative ring and let $f$ be a formal power series in two variables over $W$, i.e. an element of `MvPowerSeries (Fin 2) W`, written informally as $f \in W[[u,v]]$ with $u = X_0$ and $v = X_1$. The assertion is that there exist power series $A$ and $B$ in `MvPowerSeries (Fin 2) W`, each invariant under the relabelling of variables induced by the transposition of the two indices $0$ and $1$ — that is, $A$ and $B$ are fixed by the ring endomorphism `MvPowerSeries.rename` applied to the permutation `Equiv.swap (0 : Fin 2) 1`, so each is a symmetric power series in $u$ and $v$ — such that $$f = A + B \cdot X_0,$$ the product being taken in the power series ring. No hypothesis is placed on $W$ beyond commutativity; in particular $2$ need not be invertible. Thus $\{1, u\}$ generates $W[[u,v]]$ as a module over its subring of symmetric power series.
--
--   This is the rank-two decomposition of the two-variable power series ring over its subring of symmetric series, with the symmetric basis $\{1,u\}$; over a general commutative ring one divides the antisymmetric part, which vanishes on the diagonal, exactly by $u - v$ rather than halving. It feeds the identification of the $uv$-crossing model $W[[u,v]]/(uv-\pi)$ as a quadratic extension of its branch-exchange-invariant subring, used in [`ModularCurve.UVCrossingModel.exists_ringEquiv_adjoinRoot`](thm.html#ModularCurve.UVCrossingModel.exists_ringEquiv_adjoinRoot) and its variant for precomplete coefficient rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_rename_swap_eq_add_mul_X.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPowerSeries.exists_rename_swap_eq_add_mul_X {W : Type*} [CommRing W] (f : MvPowerSeries (Fin 2) W) : ∃ A B : MvPowerSeries (Fin 2) W, MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) A = A ∧ MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) B = B ∧ f = A + B * MvPowerSeries.X 0 := by sorry
