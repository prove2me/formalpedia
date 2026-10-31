-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_15_lp_closed_forms
-- name    : KallMayerSLP.Bonferroni.eq_3_15_lp_closed_forms
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:58.14736+00:00
-- url     : https://prove2.me/theorems/ea643b35-4a35-4455-a40f-d85861a22b36
-- title:
--   Optimal solutions of (3.14) exist, with the values of (3.15)
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, with binomial moments $S_1,S_2$: if $S_1>0$, the minimum of $v_1+\dots+v_r$ over the feasible set of (3.14) is attained and equals
--   $$
--   \frac{2}{k^*+1}S_1-\frac{2}{k^*(k^*+1)}S_2,\qquad k^*=\left\lfloor\frac{2S_2}{S_1}\right\rfloor+1,
--   $$
--   and the maximum is attained and equals
--   $$
--   S_1-\frac{2}{r}S_2.
--   $$
--   The book states these closed forms and refers to Kall and Wallace for the derivation.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
--   - encoding: $k^*$ written without a condition on $S_1$ → the statements about $k^*$ assume $0<S_1$; reason: $k^*$ divides by $S_1$ and is undefined at $S_1=0$, where every $B_i$ is null; the condition excludes only that undefined case
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.15), p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_lpObjectiveValues
import Definitions.Def_KallMayerSLP_Bonferroni_vMinClosedForm
import Definitions.Def_KallMayerSLP_Bonferroni_vMaxClosedForm

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The linear program (3.14) and its maximization counterpart have optimal solutions, with the
optimal values of (3.15): if `S₁ > 0`, the minimum of `v₁ + ⋯ + v_r` over the feasible set is
`2/(k*+1) S₁ - 2/(k*(k*+1)) S₂`, and the maximum is `S₁ - (2/r) S₂`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.15), p.288 (PDF 297).

**Formalization Note.** `IsLeast` and `IsGreatest` say that the optimum is attained by a feasible
point. They imply the corresponding equalities for `lpMin` and `lpMax`. The book's `k*` needs
`S₁ > 0`; the maximum needs no such hypothesis. -/
theorem eq_3_15_lp_closed_forms {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    (0 < binomialMoment μ B 1 →
      IsLeast (lpObjectiveValues r (binomialMoment μ B 1) (binomialMoment μ B 2))
        (vMinClosedForm (binomialMoment μ B 1) (binomialMoment μ B 2))) ∧
    IsGreatest (lpObjectiveValues r (binomialMoment μ B 1) (binomialMoment μ B 2))
      (vMaxClosedForm r (binomialMoment μ B 1) (binomialMoment μ B 2)) := by sorry

end KallMayerSLP.Bonferroni
