-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyPosNegJumpSumsIndepV1
-- name    : Kyprianou.Ch02.bvLevyPosNegJumpSumsIndepV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:43:39.316273+00:00
-- url     : https://prove2.me/theorems/6f84896f-0cb8-43bd-97d5-760e7283352e
-- title:
--   Independence of positive and negative jump-sum processes of a bounded-variation Lévy process
-- statement:
--   Let $(\Omega, \mathcal{F}, P)$ be a probability space carrying a real-valued Lévy process $X = (X_t)_{t \ge 0}$ whose sample paths have locally bounded variation on $[0, \infty)$ almost surely. Define the cumulative positive and negative jump processes
--
--   $$
--   J_t^+(\omega) := \sum_{0 < s \le t} \max\bigl(X_s(\omega) - X_{s-}(\omega),\, 0\bigr), \qquad
--   J_t^-(\omega) := \sum_{0 < s \le t} \max\bigl(X_{s-}(\omega) - X_s(\omega),\, 0\bigr).
--   $$
--
--   Then the path-valued random elements $\omega \mapsto (t \mapsto J_t^+(\omega))$ and $\omega \mapsto (t \mapsto J_t^-(\omega))$ in $\mathbb{R}^{[0, \infty)}$ are independent under $P$:
--
--   $$
--   (J_t^+)_{t \ge 0} \;\perp\!\!\!\perp\; (J_t^-)_{t \ge 0}.
--   $$
--
--   This captures the Lévy–Itô jump-measure splitting between the disjoint mark regions $(0, \infty)$ and $(-\infty, 0)$ at the path-process level on the original probability space $(\Omega, P)$.
--
--   **Formalization Note** Process-level independence is expressed via `ProbabilityTheory.iIndepFun` indexed by `Fin 2` into the product measurable space `ℝ≥0 → ℝ`.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 2, Exercise 2.8, p. 59

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem bvLevyPosNegJumpSumsIndepV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
          X s.1 ω) 0
    ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Jpos t ω else Jneg t ω) P := by sorry

end Kyprianou.Ch02
