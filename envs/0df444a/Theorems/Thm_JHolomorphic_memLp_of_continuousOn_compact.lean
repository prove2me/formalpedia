-- Prove2me | Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
-- name    : JHolomorphic.memLp_of_continuousOn_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:35:28.116365+00:00
-- url     : https://prove2.me/theorems/e1c54b90-04eb-4d3a-959a-95c59e0c1e57
-- title:
--   Continuous maps on a compact subset of $\mathbb{C}$ are in $L^p$
-- statement:
--   Let $K\subset\mathbb{C}$ be compact, $X$ a normed group, $0<p\le\infty$, and $f:\mathbb{C}\to X$ continuous on $K$. Then $f\in L^p(K)$ for Lebesgue measure restricted to $K$.
--
--   A convenience statement used to verify local integrability hypotheses for continuous data.
--
--   **Formalization Note** Membership is `MemLp f p (volume.restrict K)` with `p : ℝ≥0∞`; continuity is `ContinuousOn f K`.
-- source:
--   Standard; Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- A map that is continuous on a compact `K ⊆ ℂ` lies in `L^p(K)` for every `p`. -/
theorem memLp_of_continuousOn_compact {X : Type*} [NormedAddCommGroup X] {K : Set ℂ}
    (hK : IsCompact K) {p : ℝ≥0∞} {f : ℂ → X} (hf : ContinuousOn f K) :
    MemLp f p (volume.restrict K) := by
  sorry

end JHolomorphic
