-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_2
-- name    : LostSalesExpGap.ConstOrder.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:04.415122+00:00
-- url     : https://prove2.me/theorems/a8b32d7c-e00f-4367-8b8f-c2c967e9b256
-- title:
--   Lemma 2, p. 11 — OPT(L) ≥ C_L(r_L) and the decomposition (5) of C(π_r∞) − OPT(L)
-- statement:
--   In the lost-sales model with lead time $L\ge1$, costs $h,p>0$ and i.i.d. nonnegative demand $D$ with finite mean and strictly positive variance, let $I^r_L=\max_{j=0,\dots,L}(jr-\sum_{i=1}^jD_i)$, $C_L(r)=h\mathbb E[I^r_L]+p\mathbb E[D]-pr$, $r_L$ the least minimizer of $C_L$ on $[0,\mathbb E[D]]$, $r_\infty$ the best constant order and $I^r_\infty=\sup_{j\ge0}(jr-\sum_{i=1}^jD_i)$. Then $\mathrm{OPT}(L)\ge C_L(r_L)$, the quantities $C(\pi_{r_\infty})$, $\mathrm{OPT}(L)$ and $\mathbb E[I^{r_\infty}_\infty]$ are finite, and
--   $$
--   C(\pi_{r_\infty})-\mathrm{OPT}(L)\le h\big(\mathbb E[I^{r_\infty}_\infty]-\mathbb E[I^{r_\infty}_L]\big)+h\big(\mathbb E[I^{r_\infty}_L]-\mathbb E[I^{r_L}_L]\big)-p\,(r_\infty-r_L).
--   $$
--
--   The first term is the convergence gap of the queue to steady state, bounded by Lemma 3; the remaining terms are (6), bounded via Lemmas 4 and 5.
--
--   **Formalization Note** $\mathrm{OPT}(L)$ ranges over all measurable history-dependent randomized policies, a class containing the paper's $\Pi$, so $\mathrm{OPT}(L)\ge C_L(r_L)$ is at least as strong as printed. The finiteness of the three extended-real quantities is part of the conclusion, after which (5) is a real inequality. The printed three-term right-hand side is kept as is.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Lemma 2, eq. (5), p. 11

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Lemma 2, p. 11: `OPT(L) ≥ C_L(r_L)`, and (5)
`C(π_{r∞}) − OPT(L) ≤ h(E[I^{r∞}_∞] − E[I^{r∞}_L]) + h(E[I^{r∞}_L] − E[I^{r_L}_L]) − p(r∞ − r_L)`.
The three extended-real quantities on the left and right are first asserted finite. -/
theorem lemma_2 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ENNReal.ofReal (CL P c (rL P c c.L) c.L) ≤ CappedBaseStock.OPT P c ∧
      constCost P c (rInf P c) ≠ ⊤ ∧ CappedBaseStock.OPT P c ≠ ⊤ ∧ EIinf P (rInf P c) ≠ ⊤ ∧
      (constCost P c (rInf P c)).toReal - (CappedBaseStock.OPT P c).toReal ≤
        c.h * ((EIinf P (rInf P c)).toReal - EIL P (rInf P c) c.L) +
          c.h * (EIL P (rInf P c) c.L - EIL P (rL P c c.L) c.L) -
          c.p * (rInf P c - rL P c c.L) := by sorry

end LostSalesExpGap.ConstOrder
