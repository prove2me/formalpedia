-- Prove2me | Theorems.Thm_OAI_QuinticLienard_Sharpness_sharpness
-- name    : OAI.QuinticLienard.Sharpness.sharpness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:10:24.319465+00:00
-- url     : https://prove2.me/theorems/7b67253c-8fb5-40f6-ac07-7ea69a4b1bdf
-- title:
--   Some quintic Liénard system has exactly two limit cycles (OpenAI quintic Liénard, Theorem 1.1, sharpness)
-- statement:
--   For a real polynomial $G$, consider the planar system $\dot x = y - G(x)$, $\dot y = -x$ on $\mathbb R^2$ (`vectorField`, from the published bundle `Def_QuinticLienard`). A solution is a differentiable curve $z : \mathbb R \to \mathbb R^2$ with $z'(t)$ equal to the vector field at $z(t)$ for every $t$ (`IsSolution`). A periodic orbit is the range of a solution that is periodic with some period $T > 0$ and not constant (`IsPeriodicOrbit`). A limit cycle is a periodic orbit $C$ with an open set $U \supseteq C$ such that every periodic orbit contained in $U$ equals $C$ (`IsLimitCycle`).
--
--   **The statement.** There is a real polynomial $G$ with $\deg G \le 5$ whose system has exactly two limit cycles: the set of its limit cycles has extended cardinality $2$.
--
--   This is the sharpness half of the paper's Theorem 1.1 (proved in its Section 7) and the second conjunct of the goal `OAI.QuinticLienard.main`.
--
--   Lean: `OAI.QuinticLienard.Sharpness.sharpness`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LienardCycles/SharpCycles.lean`).
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf, Theorem 1.1 and Section 7; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LienardCycles/SharpCycles.lean (declaration OAI.QuinticLienard.Sharpness.sharpness)

import Mathlib
import Definitions.Def_QuinticLienard

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
lemma sharpness : ∃ G : Polynomial ℝ,G.degree≤5 ∧ {C : Set Plane | IsLimitCycle G C}.encard=2 := by
  sorry
end QuinticLienard.Sharpness

end OAI
end
