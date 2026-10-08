-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_lemma2_5_bounded_value_difference
-- name    : LostSalesLearning.ValueGap.lemma2_5_bounded_value_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:18:58.182624+00:00
-- url     : https://prove2.me/theorems/85fcdf92-5653-40f8-a227-594d36277496
-- title:
--   Lemma 2.5, p. 8 — for any x, T and s, s′ ∈ S^x, V^x_T(s) − V^x_T(s′) ≤ 36 max(h,p)Lx
-- statement:
--   Consider a single-product periodic-review inventory system with lost sales, a deterministic lead time of $L\ge 0$ periods, and a base-stock (order-up-to) policy with level $x$. A state $\mathbf s=(s(0),\dots,s(L))$ records the on-hand inventory $s(0)$ and the outstanding orders $s(1),\dots,s(L)$, and $\mathcal S^x$ is the set of nonnegative states whose entries sum to $x$. Demands are i.i.d. with an arbitrary law $F$ on $[0,\infty)$. Each period sells $y_t=\min\{s_t(0),d_t\}$ and incurs the pseudo-cost $C^x_t=h(s_t(0)-y_t)-p\,y_t$, with holding cost $h\ge 0$ and lost-sales penalty $p\ge 0$ per unit, and $V^x_T(\mathbf s)=\mathbb E[\sum_{t=1}^{T}C^x_t\mid\mathbf s_1=\mathbf s]$ is the value over horizon $T$.
--
--   Then for any $x$, any horizon $T$ and any two states $\mathbf s,\mathbf s'\in\mathcal S^x$,
--   $$V^x_T(\mathbf s)-V^x_T(\mathbf s')\le 36\max(h,p)\,L\,x .$$
--
--   The bound is uniform in the horizon and linear in the lead time. It is the key structural fact behind the paper's regret analysis: it bounds the bias of the base-stock Markov reward process and shows that its long-run average cost does not depend on the starting state. For $L=0$ both sides are $0$, since $\mathcal S^x$ then has the single state $(x)$.
--
--   **Formalization Note** The value is the expectation of the summed pseudo-costs under the product law of the demand path (Definition 2.4, in the form used on p. 8, equal by the tower property). The costs $h,p$ are nonnegative, the reading of "per unit holding cost and per unit lost sales penalty" in §1.1. No assumption is placed on $F$ beyond being a probability law on $[0,\infty)$: the assumptions $F(0)>0$ and bounded demand of the paper's other results are not needed here.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 8, Lemma 2.5; proof pp. 8–9

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem lemma2_5_bounded_value_difference {L : ℕ} (h p x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (T : ℕ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) :
    value h p F T s - value h p F T s' ≤ 36 * max h p * (L : ℝ) * x := by sorry

end LostSalesLearning.ValueGap
