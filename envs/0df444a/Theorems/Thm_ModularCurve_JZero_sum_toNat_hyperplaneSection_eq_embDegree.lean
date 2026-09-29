-- Prove2me | Theorems.Thm_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree
-- name    : ModularCurve.JZero.sum_toNat_hyperplaneSection_eq_embDegree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/9e02c7ee-b97d-5288-bf7a-342bfdc95604
-- title:
--   Hyperplane sections of the embedding system have degree 2g+1
-- statement:
--   Let $N$ be a positive natural number and write $\bar F_N$ for `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the image of `modularFunctionFieldFull N` under coefficientwise extension of scalars. Put $g =$ `genusFF` $(\overline{\mathbb Q}, \bar F_N)$, the $\overline{\mathbb Q}$-dimension of $H^1$ of the zero divisor, so that `embDegree N` $= 2g+1$ and `embDivisor N` is the divisor $(2g+1)\cdot[\,\overline{\infty}\,]$ supported at the place `cuspInftyBar N`. Let $r$ be a natural number and $s : \mathrm{Fin}\,r \to \bar F_N$ a family satisfying `IsEmbBasis N s`, that is, $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space $\{f : v(f) \le \exp(\mathrm{embDivisor}\,N\,(v)) \text{ for all places } v\}$. Let $a : \mathrm{Fin}\,r \to \overline{\mathbb Q}$ be coefficients with $\mathrm{linSec}\,s\,a = \sum_i a_i \cdot s_i \neq 0$, and let $Za$ be a divisor of $\bar F_N / \overline{\mathbb Q}$ such that for every place $w$ one has $Za(w) = \mathrm{ord}_w(\mathrm{linSec}\,s\,a) + (\mathrm{embDivisor}\,N)(w)$, where $\mathrm{ord}_w(f) = -\log$ of the adic valuation of $f$ at $w$. Then the sum over the support of $Za$ of the truncations $Za(w)^{+} = \max(Za(w),0)$ to $\mathbb N$ equals `embDegree N` $= 2g+1$.
--
--   This is the statement that a hyperplane section of the projective model of $X_0(N)$ given by a basis of $L((2g+1)\overline{\infty})$ is an effective zero-cycle of total multiplicity $2g+1$, the degree of the model. It supplies the normalisation of degrees used in the height-form estimates on $J_0(N)$, among them [`ModularCurve.JZero.exists_hyperplaneSection_defect_le`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_defect_le) and [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.JZero.sum_toNat_hyperplaneSection_eq_embDegree (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0)
    (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) :
    (Za.sum fun _ n => n.toNat) = embDegree N := by sorry
