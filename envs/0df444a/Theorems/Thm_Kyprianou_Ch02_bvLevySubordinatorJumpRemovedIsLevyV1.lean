-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevySubordinatorJumpRemovedIsLevyV1
-- name    : Kyprianou.Ch02.bvLevySubordinatorJumpRemovedIsLevyV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:27:52.157799+00:00
-- url     : https://prove2.me/theorems/a6866324-b69b-4f14-bedc-85cb207e9863
-- title:
--   Jump-removed residual of a Lévy subordinator is Lévy
-- statement:
--   Let $Y$ be a real Lévy process that is almost surely monotone (a Lévy subordinator). Define the cumulative positive jump sum
--   $$
--   J_t(\omega)=\sum_{0<s\le t}\max\bigl(Y_s(\omega)-Y_{s-}(\omega),0\bigr)
--   $$
--   and the jump-removed residual $R_t=Y_t-J_t$. Then $R$ is again a Lévy process under $P$.
--
--   This records that removing the pure-jump part of a subordinator preserves the Lévy axioms (independent and stationary increments, càdlàg paths, start at zero), so the residual can be analysed separately as a continuous Lévy process.
--
--   **Formalization Note.** The residual is written inline without `let`-bindings so that importers can unify it directly with `Y - J`.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes with Applications, Springer 2014, Chapter 2, Lévy-Itô decomposition for subordinators: after removing the Poisson jump measure the residual process remains Lévy.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevySubordinatorJumpRemovedIsLevyV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℝ≥0 → Ω → ℝ)
    (hY : ProbabilityTheory.IsLevyProcess Y P)
    (hMono : ∀ᵐ ω ∂P, Monotone (fun t => Y t ω)) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω =>
        Y t ω -
          ∑' s : Set.Ioc (0 : ℝ≥0) t,
            max (Y s.1 ω -
              Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Y u ω)) 0)
      P := by sorry
