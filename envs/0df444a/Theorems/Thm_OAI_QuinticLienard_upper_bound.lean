-- Prove2me | Theorems.Thm_OAI_QuinticLienard_upper_bound
-- name    : OAI.QuinticLienard.upper_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:10:24.685626+00:00
-- url     : https://prove2.me/theorems/7dc6807a-c628-4638-9995-ce09a6b03bd3
-- title:
--   A quintic Liénard system has at most two limit cycles (OpenAI quintic Liénard, Theorem 1.1, upper bound)
-- statement:
--   For a real polynomial $F$, consider the planar system $\dot x = y - F(x)$, $\dot y = -x$ on $\mathbb R^2$ (`vectorField`, from the published bundle `Def_QuinticLienard`). A solution is a differentiable curve $z : \mathbb R \to \mathbb R^2$ with $z'(t)$ equal to the vector field at $z(t)$ for every $t$ (`IsSolution`). A periodic orbit is the range of a solution that is periodic with some period $T > 0$ and not constant (`IsPeriodicOrbit`). A limit cycle is a periodic orbit $C$ with an open set $U \supseteq C$ such that every periodic orbit contained in $U$ equals $C$ (`IsLimitCycle`).
--
--   **The statement.** If $\deg F \le 5$, then the set of limit cycles has extended cardinality at most $2$:
--   $$\#\{C \subseteq \mathbb R^2 : C \text{ is a limit cycle of } \dot x = y - F(x),\ \dot y = -x\} \le 2.$$
--
--   This is the upper-bound half of the paper's Theorem 1.1 and the first conjunct of the goal `OAI.QuinticLienard.main`.
--
--   Lean: `OAI.QuinticLienard.upper_bound`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LienardCycles/UpperAssembly.lean`).
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf, Theorem 1.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LienardCycles/UpperAssembly.lean (declaration OAI.QuinticLienard.upper_bound)

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
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
lemma upper_bound (F : Polynomial ℝ) (hF : F.degree≤5) : {C : Set Plane | IsLimitCycle F C}.encard≤2 := by
  sorry
end QuinticLienard

end OAI
end
