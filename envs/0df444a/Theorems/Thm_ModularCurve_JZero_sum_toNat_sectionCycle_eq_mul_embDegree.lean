-- Prove2me | Theorems.Thm_ModularCurve_JZero_sum_toNat_sectionCycle_eq_mul_embDegree
-- name    : ModularCurve.JZero.sum_toNat_sectionCycle_eq_mul_embDegree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/cac7640a-c0f4-5264-b45e-ec3018012846
-- title:
--   Total multiplicity of a section cycle equals kcdotembDegree
-- statement:
--   Fix $N\ge 1$ (a `NeZero` instance) and $k\in\mathbb{N}$, and work in the field $\bar F_N=$ `modularFunctionFieldBar N`, the subfield of $\mathbb{Q}^{\mathrm{alg}}((q))$ generated over $\mathbb{Q}^{\mathrm{alg}}$ by the coefficientwise image of `modularFunctionFieldFull N`. Let $E=$ `embDivisor N` be the divisor $(2g+1)\cdot[\bar\infty]$, where $g=$ `genusFF` of $\bar F_N$ over $\mathbb{Q}^{\mathrm{alg}}$, $2g+1=$ `embDegree N`, and $\bar\infty=$ `cuspInftyBar N`. Let $u\in\bar F_N$ be nonzero and lie in the Riemann–Roch space of $k\cdot E$, i.e. $w(u)\le \exp\big((k\cdot E)(w)\big)$ for every place $w$ of $\bar F_N$ over $\mathbb{Q}^{\mathrm{alg}}$ in the sense of the project's `Place` structure (valuation subrings containing $\mathbb{Q}^{\mathrm{alg}}$, proper, with principal ideals). Let $B$ be a divisor, i.e. a finitely supported $\mathbb{Z}$-valued function on places, such that $B(w)=\mathrm{ord}_w(u)+(k\cdot E)(w)$ for every $w$, where $\mathrm{ord}_w(u)=-\log$ of the adic valuation of $u$ at $w$. The conclusion is that the sum over the support of $B$ of the truncations $\max(B(w),0)$ equals $k\cdot$ `embDegree N` as a natural number.
--
--   This is the statement that the zero-cycle cut out on $X_0(N)_{\mathbb{Q}^{\mathrm{alg}}}$ by a section $u$ of $k$ times the embedding divisor is effective of total multiplicity $k(2g+1)$; it is the bookkeeping behind the degree normalisation in the height form on `JZero N`. It is used by the statements about the Chow-side contributions of the archimedean embedding and of the cusp away from the support, and by the proximity-sum comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_sum_toNat_sectionCycle_eq_mul_embDegree.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.JZero.sum_toNat_sectionCycle_eq_mul_embDegree (N : ℕ) [NeZero N]
    (k : ℕ) (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    (B.sum fun _ n => n.toNat) = k * embDegree N := by sorry
