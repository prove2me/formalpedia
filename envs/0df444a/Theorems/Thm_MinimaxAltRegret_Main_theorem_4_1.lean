-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_theorem_4_1
-- name    : MinimaxAltRegret.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:37.681575+00:00
-- url     : https://prove2.me/theorems/84b4c5c2-435b-4def-9133-ec57e067bc68
-- title:
--   Theorem 4.1 — worst-domain OCO lower bound
-- statement:
--   Fix c_0=1/(80 log 65536) and c=min(c_0/6,1/4)>0. For every d>=2 and every positive integer horizon T, there is a full-dimensional compact convex X in R^d, selected before the learner, such that every possibly randomized full-information learner admits a fixed oblivious sequence of continuous convex functions f_1,...,f_T:X to [0,1] satisfying
--
--   $$\mathbb E[R_T]\ge c\,d\log(1+T/d).$$
--
--   The expectation includes only learner randomness, with the hindsight supremum already taken. For m=floor(d/2), the displayed witness X is the product of m disks and, in odd dimension, an unused interval when T>=5m, and is [-1,1]^d when T<5m. The hard loss sequence can depend on the learner; X cannot. This is a worst-domain lower bound, not a lower bound for every domain.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a possibly randomized full-information learner and its internal expectation → an arbitrary probability space, a measurable seed-based HistoryLearner on all finite revealed-loss histories, and an explicitly integrable regret random variable; reason: this gives the stated nonanticipating learner and a genuine bounded expectation, with the hindsight supremum inside the integral
--   - encoding: a d-dimensional compact convex set X and convex functions defined on X → a compact convex subset of EuclideanSpace R (Fin d) with nonempty interior, and ambient functions restricted by ConvexOn and pointwise bounds on X; reason: nonempty interior is exactly full affine dimension; arbitrary extensions outside X change no source instance, and no continuity is required on the boundary
--   - generalization: a positive universal c and an existential full-dimensional compact convex domain → c=min(1/(480 log 65536),1/4) and X equal to the proof-computed hardDomain(d,T); reason: the two regimes of the source proof provide exactly these domains and constants, uniformly including odd d and all T>=1
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 10 / PDF p. 11, Theorem 4.1, Eq. (14); proof printed pp. 20--22 / PDF pp. 21--23; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Sampling
import Definitions.Def_MinimaxAltRegret_Main_LowerConstruction

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem theorem_4_1 :
  0 < ocoConstant ∧ ∀ (d T : ℕ), 2 ≤ d → 1 ≤ T →
  ∃ X : Set (Point d), X = hardDomain d T ∧ convexBody X ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (learner : HistoryLearner X (Point d → ℝ) Ω),
      ∃ f : ℕ → Point d → ℝ, continuousLosses01 X T f ∧
        Integrable (fun ω => alternatingRegret X T f
          (fun t => (response learner f t ω).val)) μ ∧
        ocoConstant*(d : ℝ)*Real.log (1+(T : ℝ)/(d : ℝ)) ≤
          ∫ ω, alternatingRegret X T f (fun t => (response learner f t ω).val) ∂μ := by sorry

end MinimaxAltRegret.Main
