-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_configuration
-- name    : OAI.GaussianPropeller.Reduction.exists_configuration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:19:36.277406+00:00
-- url     : https://prove2.me/theorems/65693223-4052-4d3d-9ed5-d7471846a4d7
-- title:
--   A minimal optimal Gaussian partition with value above 9/(8π) and no null cell yields a Configuration (OpenAI Gaussian propeller)
-- statement:
--   Let $d$ and $k \ge 2$ be natural numbers (with `[NeZero k]`), let $E = \mathbb R^d$ be `Space d` (`EuclideanSpace ℝ (Fin d)`) and $\gamma_d$ its standard Gaussian measure (`gaussian d`, Mathlib's `stdGaussian`).
--
--   Definitions used (the first three from the published bundle `Def_GaussianPropeller`):
--   - `IsPartition A` for $A : \mathrm{Fin}\ k \to \mathrm{Set}\ E$: every cell is measurable and almost every point lies in exactly one cell.
--   - `centroid S` $= \int_S x\,d\gamma_d(x)$ and `value A` $= \sum_i \|\mathrm{centroid}(A_i)\|^2$.
--   - `Optimal A`: $A$ is a partition and `value B ≤ value A` for every partition $B$ with $k$ cells.
--   - `activeCount A`: the number of cells with $\gamma_d(A_i) \ne 0$. `MinimalOptimal A`: $A$ is optimal and `activeCount A ≤ activeCount B` for every optimal $B$.
--   - `Configuration d k`: as in the statement `OAI.GaussianPropeller.Reduction.Configuration.impossible_four` of this split — vectors $z_j$ and weights $P_j$ with $\sum z_j = 0$, $\sum\|z_j\|^2 = 1$, $z_j \ne 0$, $\|z_j\|$ non-increasing, pairwise negative inner products, $\|z_j\| \le 2/3$, $\sum P_j = 1$, $P_j \le 1/2$, $c_k\|z_j\|^2 \le P_j$ ($c_k = 0.929$ if $k = 5$, else $0.884$) and $0.415\|z_j\| + 0.15\|z_j\|^2 \le P_j$, together with the conditions `pair`, `cap3` and `loss4` spelled out there.
--
--   Let $A$ be a `MinimalOptimal` partition with $\frac{9}{8\pi} < $ `value A` and $\gamma_d(A_j) \ne 0$ for every $j$. Then `Configuration d k` is nonempty.
--
--   Lean: `OAI.GaussianPropeller.Reduction.exists_configuration`, OpenAI's lemma of that name (in `lean/OAI/Probability/GaussianPropeller/Configuration.lean`). `Space`, `gaussian`, `IsPartition`, `centroid` and `value` come from the published bundle `Def_GaussianPropeller`; `Reduction.Optimal`, `Reduction.activeLabels`, `Reduction.activeCount`, `Reduction.MinimalOptimal` and `Reduction.Configuration` from the definitions bundle `OAIQWGP000` of this split.
-- source:
--   OpenAI, The Gaussian propeller bound in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 096; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianPropeller/Configuration.lean (declaration OAI.GaussianPropeller.Reduction.exists_configuration)

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell ProbabilityBounds
open scoped RealInnerProductSpace

variable {d k:ℕ} [NeZero k]

lemma exists_configuration (hk:2≤k) {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) :
    Nonempty (Configuration d k) := by
  sorry

end GaussianPropeller.Reduction

end OAI
end
