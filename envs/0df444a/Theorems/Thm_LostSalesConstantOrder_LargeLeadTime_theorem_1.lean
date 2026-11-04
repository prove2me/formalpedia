-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_theorem_1
-- name    : LostSalesConstantOrder.LargeLeadTime.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:17.606391+00:00
-- url     : https://prove2.me/theorems/83f01b77-d16c-4161-951d-3e923823d0fa
-- title:
--   Theorem 1: $\pi_z$ costs at most $(1+\epsilon)\,\mathrm{OPT}(L,T)$ once $L\ge y(\epsilon)$ and $T\ge(1+3\epsilon^{-1})L$
-- statement:
--   Consider the periodic-review lost-sales inventory system with holding cost $h>0$, lost-demand penalty $c>0$, lead time $L\ge1$, and i.i.d. nonnegative demands with law $\mathcal D$ that has a finite third moment and is not deterministic. Let $z$ be the best constant order quantity, $z=\arg\min_{v\ge0}(h\mathbb E[I^v_\infty]-cv)$, and $\pi_z$ the constant-order policy that orders $I^z_\infty+z$ in the first period and $z$ in every later period. For all $\epsilon\in(0,1)$, $L\ge y(\epsilon)$ and $T\ge(1+3\epsilon^{-1})L$,
--   $$
--   \frac{\mathbb E\big[\sum_{t=L+1}^{T+L}C^{\pi_z}_t\big]}{\mathrm{OPT}(L,T)}\ \le\ 1+\epsilon,
--   $$
--   where $\mathrm{OPT}(L,T)$ is the optimal value of problem (1) and
--   $$
--   y(\epsilon)=\max\Big(2^{14}h(Q+2^{3/2}\mathbb E[D])(\mathbb E^2[D]+\mathbb E[D^2])^3\sigma^{-6}m^3g^{-1}\epsilon^{-1},\ \big(12c\,\mathbb E[D]\,g^{-1}((2ch^{-1})^{1/2}+3)\big)^2\epsilon^{-2}\Big).
--   $$
--
--   The simplest open-loop policy, which ignores the state entirely, is within a factor $1+\epsilon$ of optimal once the lead time is large, with an explicit threshold.
--
--   **Formalization Note** The ratio is stated multiplicatively, $\mathbb E[\sum C^{\pi_z}_t]\le(1+\epsilon)\,\mathrm{OPT}(L,T)$ in $[0,\infty]$; this is the paper's ratio because $0<Tg\le\mathrm{OPT}(L,T)<\infty$. OPT is the infimum over the model's history-dependent randomized policies, which contain the paper's class $\Pi$, so the statement is at least as strong as the page's. The second term of $y(\epsilon)$ carries the factor $\mathbb E[D]$ that the page omits (p. 5): the proof on p. 15 needs it, because it bounds the second term of Corollary 12, whose proof yields $\mathcal I^*\le(\lceil(2ch^{-1}L)^{1/2}\rceil+2)\mathbb E[D]$; without it the threshold is not invariant under rescaling the demand. The periods $t=L+1,\dots,T+L$ are Lean periods $L,\dots,T+L-1$.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 6, Theorem 1 (y(ϵ) of p. 5 with E[D] restored in its second term)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Theorem 1, p. 6, with `y(ϵ)` corrected (the factor `E[D]` of its second term restored, see
`yEps`). For all `ϵ ∈ (0, 1)`, `L ≥ y(ϵ)` and `T ≥ (1 + 3ϵ⁻¹)L`, the constant-order policy `π_z`
satisfies `E[Σ_{t=L+1}^{T+L} C_t^{π_z}] ≤ (1 + ϵ) OPT(L, T)`. This is the page's ratio bound
`E[Σ C_t^{π_z}] / OPT(L, T) ≤ 1 + ϵ`, stated multiplicatively (`0 < OPT(L, T) < ∞`). -/
theorem theorem_1 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hL : yEps P prm ε ≤ prm.L)
    (T : ℕ) (hT : (1 + 3 / ε) * prm.L ≤ T) :
    costLT P prm (constantOrderPolicy P (zStar P prm)) T ≤
      ENNReal.ofReal (1 + ε) * optLT P prm T := by sorry

end LostSalesConstantOrder.LargeLeadTime
