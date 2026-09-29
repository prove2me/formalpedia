-- Prove2me | Theorems.Thm_InformationTheory_klDiv_trim_le
-- name    : InformationTheory.klDiv_trim_le
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T20:08:19.424446+00:00
-- url     : https://prove2.me/theorems/97326b18-7771-4cac-8527-f1958e68ed0b
-- title:
--   KL divergence decreases under restriction to a sub-$\sigma$-algebra
-- statement:
--   Let $P$ and $Q$ be probability measures on a measurable space $(\Omega,\mathcal F)$, and let $\mathcal G\subseteq\mathcal F$ be a sub-$\sigma$-algebra. Restrict both measures to $\mathcal G$. Then
--
--   $$
--   D\!\left(P|_{\mathcal G}\,\middle\Vert\,Q|_{\mathcal G}\right)
--   \le
--   D(P\Vert Q).
--   $$
--
--   This is the data-processing inequality for forgetting information: observing only events in a smaller sigma-algebra cannot increase relative entropy. It is reusable for stopped experiments, sufficient statistics, coarse observations, and finite-horizon projections.
--
--   **Formalization Note** Restriction to a sub-sigma-algebra is represented by `Measure.trim`. Both divergences are extended nonnegative real numbers, so the statement includes singular and infinite-divergence cases.
-- source:
--   Standard relative-entropy data-processing inequality; specialized to stopped bandit experiments in Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 15.7, printed p. 211. Formal ingredients: Mathlib `MeasureTheory.rnDeriv_trim` and conditional Jensen inequality `ConvexOn.map_condExp_le`.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem InformationTheory.klDiv_trim_le {α : Type*} {m m₀ : MeasurableSpace α}
    (hm : m ≤ m₀) (μ ν : @Measure α m₀)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    @klDiv α m (μ.trim hm) (ν.trim hm) ≤ @klDiv α m₀ μ ν := by
  sorry
