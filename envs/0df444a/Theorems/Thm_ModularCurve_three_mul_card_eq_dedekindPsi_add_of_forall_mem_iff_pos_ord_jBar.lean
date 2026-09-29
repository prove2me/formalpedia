-- Prove2me | Theorems.Thm_ModularCurve_three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar
-- name    : ModularCurve.three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/fdcde604-b3ca-528c-80d0-5a932fbcf605
-- title:
--   Counting places where jmath̄ vanishes, for odd N
-- statement:
--   Let $N$ be a nonzero natural number which is odd. Work with the field $F_N$ obtained as follows: inside $\mathrm{LaurentSeries}(\mathbb{Q})$ one forms the intermediate field `modularFunctionFieldFull N` generated over $\mathbb{Q}$ by the divisor expansions at level $N$, and $F_N=$ `modularFunctionFieldBar N` is the intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ generated over $\overline{\mathbb{Q}}$ by the image of that field under the coefficientwise embedding induced by $\mathbb{Q}\to\overline{\mathbb{Q}}$. A place $v$ of $F_N$ over $\overline{\mathbb{Q}}$ is, in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), a valuation subring of $F_N$ containing the image of $\overline{\mathbb{Q}}$, distinct from $F_N$ itself, and a principal ideal ring; for $f\in F_N$, $v.\mathrm{ord}(f)$ is minus the logarithm of the value of $f$ under the associated adic valuation. Let $\bar\jmath=$ `jBar N` be the element of $F_N$ given by the image of the $q$-expansion of $j$ under that coefficientwise embedding. Let $S_0$ be a finite set of such places with the property that a place $v$ lies in $S_0$ if and only if $v.\mathrm{ord}(\bar\jmath)>0$. The conclusion, an identity of natural numbers, is $$3\,\#S_0=\psi(N)+2\,\#\{v\in S_0:\ v.\mathrm{ord}(\bar\jmath)=1\},$$ where $\psi(N)=\sum_{d\mid N,\ d\text{ squarefree}}N/d$ is `dedekindPsi N`.
--
--   This is the count of the fibre of $j$ over $0$ on the modular curve of level $N$ over $\overline{\mathbb{Q}}$: the degree of the fibre is $\psi(N)$ and, for odd $N$, ramification there is either trivial or total of order $3$, so the number of points in the fibre is determined by the number of unramified ones. It is used to extract the elliptic-point count $\varepsilon_3$ in [`ModularCurve.card_filter_ord_jBar_eq_one_eq_nuThree`](thm.html#ModularCurve.card_filter_ord_jBar_eq_one_eq_nuThree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar (N : ℕ) [NeZero N] (hodd : Odd N) (S0 : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) (hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (jBar N)) : 3 * S0.card = dedekindPsi N + 2 * (S0.filter fun v => v.ord (jBar N) = 1).card := by sorry
