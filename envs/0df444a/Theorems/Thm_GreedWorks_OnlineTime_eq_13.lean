-- Prove2me | Theorems.Thm_GreedWorks_OnlineTime_eq_13
-- name    : GreedWorks.OnlineTime.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:38.467987+00:00
-- url     : https://prove2.me/theorems/d81472f9-0ab1-4a8a-9215-afe47a697096
-- title:
--   (13), §6.2, p. 15 — z^{P_r} ≤ (1 + ∆/2) z^{S_r} ≤ (1 + ∆/2) OPT for the relaxations with release dates
-- statement:
--   Consider a stochastic unrelated-machine instance with integer release dates, weights $w_j\ge0$, and squared coefficients of variation bounded by $\Delta$, and the time-indexed relaxations $(\mathrm S_r)$ and $(\mathrm P_r)$ built from its means $\mathbb E[P_{ij}]$ and squared coefficients of variation $\mathbb{CV}[P_{ij}]^2$. Then
--   $$z^{P_r}\;\le\;\Big(1+\frac\Delta2\Big)z^{S_r}\;\le\;\Big(1+\frac\Delta2\Big)\mathsf{OPT},$$
--   in the following form.
--
--   1. For every point $y$ feasible for $(\mathrm S_r)$ there is a point $y'$ feasible for $(\mathrm P_r)$ with $z^{P_r}(y')\le(1+\frac\Delta2)\,z^{S_r}(y)$.
--   2. For every admissible (feasible, nonanticipatory) scheduling policy $\Pi$ there is a point $y$ feasible for $(\mathrm S_r)$ with $z^{S_r}(y)\le\mathbb E\big[\sum_jw_jC^\Pi_j\big]$.
--
--   Together the two parts bound the deterministic relaxation $(\mathrm P_r)$, on which the dual fitting is done, by $(1+\frac\Delta2)$ times the expected cost of any nonanticipatory policy.
--
--   **Formalization Note** Optimal values are not formed: part 1 implies $\inf z^{P_r}\le(1+\frac\Delta2)\inf z^{S_r}$ and part 2 implies $\inf z^{S_r}\le\mathsf{OPT}$. Comparators choose machines at start time, may idle, and start at real times. Integer release dates are essential: with $r=\frac12$, one job and $P\equiv1$, $\mathsf{OPT}=\frac32$ but every point of $(\mathrm S_r)$ has value $2$.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 15, §6.2, (13); Lemma 2 and Corollary 1, p. 8

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP

namespace GreedWorks.OnlineTime

open MeasureTheory

/-- (13), §6.2, p. 15: `z^{P_r} ≤ (1 + Δ/2) z^{S_r} ≤ (1 + Δ/2) OPT`, stated without infima.
(a) Every point `y` feasible for (S_r) yields a point feasible for (P_r) whose value is at most
`(1 + Δ/2) z^{S_r}(y)`. (b) (S_r) is a relaxation: for every admissible nonanticipatory policy
there is a point feasible for (S_r) whose value is at most the policy's expected total weighted
GreedWorks.OnlineList.completion time. -/
theorem eq_13 {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) :
    (∀ y, IsFeasibleS I.eligible I.release (mean I) (cvSquared I) y →
      ∃ y', IsFeasibleP I.eligible I.release (mean I) y' ∧
        valueP I.eligible (mean I) I.weight y' ≤
          (1 + I.Delta / 2) * valueS I.eligible (mean I) (cvSquared I) I.weight y) ∧
    (∀ pol : GreedWorks.OnlineList.Policy M n, IsAdmissible I pol →
      ∃ y, IsFeasibleS I.eligible I.release (mean I) (cvSquared I) y ∧
        valueS I.eligible (mean I) (cvSquared I) I.weight y ≤ policyCost I pol) := by sorry

end GreedWorks.OnlineTime
