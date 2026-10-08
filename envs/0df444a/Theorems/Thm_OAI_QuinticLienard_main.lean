-- Prove2me | Theorems.Thm_OAI_QuinticLienard_main
-- name    : OAI.QuinticLienard.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:13.659989+00:00
-- url     : https://prove2.me/theorems/7426635e-8da0-4209-ac55-4307229b32ea
-- statement:
--   The theorem states two things about the planar Liénard-type system x' = y − F(x), y' = −x, where F is a real polynomial and the phase plane is ℝ × ℝ. A solution is a differentiable curve z: ℝ → ℝ × ℝ satisfying this system at every time. A periodic orbit is the range of a solution that is periodic with some period T > 0 and is not constant, meaning it takes at least two distinct values. A limit cycle is a periodic orbit C for which there is an open set U containing C such that every periodic orbit contained in U equals C. First, for every polynomial F of degree at most 5, the set of limit cycles of the system has extended cardinality at most 2, so there are at most two limit cycles. Second, there exists a polynomial F of degree at most 5 for which the set of limit cycles has extended cardinality exactly 2. Together these say that the maximum number of limit cycles for such systems with F of degree at most 5 is 2. The theorem is admitted in the source with its proof left as sorry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/QuinticLienard.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/QuinticLienard.lean; bytes 1098..1322
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_QuinticLienard

namespace OAI

namespace QuinticLienard

open scoped Topology NNReal ContDiff Manifold

open Filter Set

open Set Filter Metric MeasureTheory

open scoped Topology NNReal ContDiff

open scoped Topology ENNReal

open Set Filter MeasureTheory

open Set Filter Asymptotics

open Set Filter Metric

open scoped Topology NNReal

open scoped Topology

open scoped Topology ContDiff

open Set Filter

open scoped Topology ContDiff NNReal

theorem main :
    (∀ F : Polynomial ℝ, F.degree ≤ 5 → {C : Set Plane | IsLimitCycle F C}.encard ≤ 2) ∧
    (∃ F : Polynomial ℝ, F.degree ≤ 5 ∧ {C : Set Plane | IsLimitCycle F C}.encard = 2) := by
  sorry

end QuinticLienard
end OAI
