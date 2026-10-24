-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_closedBallCap_lowerSemicontinuous_408915f
-- name    : FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:21.84657+00:00
-- url     : https://prove2.me/theorems/8c4fd480-0b11-461f-9aa5-cdb5289a1173
-- title:
--   Lower Semicontinuity After Closed-Ball Capping
-- statement:
--   This proves preservation of lower semicontinuity under the closed-ball cap operation.
--
--   Let $E$ be a normed additive commutative group, let $\varphi:E\to[-\infty,\infty]$ be extended-real valued, and let $L\in[0,\infty)$. If $\varphi$ is lower semicontinuous, then `closedBallCap φ L` is lower semicontinuous:
--
--   $$
--   \operatorname{LSC}(\varphi)\Longrightarrow\operatorname{LSC}(\operatorname{closedBallCap}(\varphi,L)).
--   $$
--
--   The operation agrees with $\varphi$ on the closed ball of radius $L$ centered at $0$ and takes the value $+\infty$ outside it. The declaration is `closedBallCap_lowerSemicontinuous`; no inner-product, finite-dimensional, or measurable-space assumptions are present in the statement.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L40-L67 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous_408915f
 (φ : E → EReal) (L : NNReal)
    (hφ : LowerSemicontinuous φ) : LowerSemicontinuous (closedBallCap φ L) := by sorry
