-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_zStar_spec
-- name    : LostSalesConstantOrder.LargeLeadTime.zStar_spec
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T11:47:40.870229+00:00
-- url     : https://prove2.me/theorems/d5ce021a-3662-4eef-b52c-0b3f1c713491
-- title:
--   The best constant order $z$ is a minimizer of $h\mathbb E[I^v_\infty]-cv$ and $z<\mathbb E[D]$
-- statement:
--   Consider the lost-sales model with holding cost $h>0$, lost-demand penalty $c>0$, and i.i.d. nonnegative demands $D$ with finite third moment and a non-degenerate law. For $v\ge 0$ let $I^v_\infty=\sup_{k\ge0}\big(kv-\sum_{i=1}^kD_i\big)\in[0,\infty]$ and
--   $$f(v)=h\,\mathbb E[I^v_\infty]+c\,(\mathbb E[D]-v)^+\in[0,\infty]$$
--   (this is `zObjective`, the paper's objective $h\mathbb E[I^v_\infty]-cv$ shifted by the constant $c\,\mathbb E[D]$). Let $z$ be the infimum of the set of minimizers of $f$ over $v\ge0$ (`zStar`). Then $z$ is itself a minimizer of $f$, and $z<\mathbb E[D]$.
--
--   This is the implicit well-posedness claim behind the paper's definition $z=\arg\min_{v\ge0}(h\mathbb E[I^v_\infty]-cv)$ (p. 5) and its use of the stationary policy $\pi_z$ in Theorem 1. Why it holds: $f(0)=c\,\mathbb E[D]<\infty$. $f$ is lower semicontinuous (the supremum is a supremum of continuous functions of $v$; apply Fatou). $f(v)=\infty$ for $v\ge\mathbb E[D]$, because the walk then has nonnegative drift and is non-degenerate, so its supremum is a.s. infinite. Hence the minimizers form a nonempty closed subset of $[0,\mathbb E[D])$, and that subset contains its infimum.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 5, §3.1 (definition of z = argmin_{v≥0}(hE[I^v_∞] − cv)), used in Theorem 1 (p. 6) and its proof (p. 15, (24)-(25))

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- §3.1, p. 5: the best constant order quantity `z = argmin_{v ≥ 0} (h E[I^v_∞] − c v)` is
well defined: the infimum `zStar` of the minimizers of `zObjective` is itself a minimizer, and it
lies strictly below the mean demand `E[D]` (so `π_z` is a stable constant-order policy). -/
theorem zStar_spec (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    (zStar P prm : ℝ) < CappedBaseStock.mean P ∧
      ∀ w : ℝ≥0, zObjective P prm (zStar P prm) ≤ zObjective P prm w := by sorry

end LostSalesConstantOrder.LargeLeadTime
