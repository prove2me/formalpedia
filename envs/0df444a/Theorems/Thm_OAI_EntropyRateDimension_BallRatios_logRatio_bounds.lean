-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_BallRatios_logRatio_bounds
-- name    : OAI.EntropyRateDimension.BallRatios.logRatio_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:45:43.310402+00:00
-- url     : https://prove2.me/theorems/5aeded76-7474-4ee8-bda9-3fb9813ca81b
-- title:
--   Log ball ratios lie between zero and the log envelope
-- statement:
--   For measures $\mu,\nu$ on $\mathbb R$, let $M(x)=\sup_q\mu(\bar B(x,q))/\nu(\bar B(x,q))$ over rational radii $0<q\le1$, the log envelope $\max(0,\log M(x))$, and the log ratio $\log\bigl(\mu(\bar B(x,r))/\nu(\bar B(x,r))\bigr)$.
--
--   Let $\mu,\nu$ be finite with $\nu\le\mu$. Then for $\nu$-almost every $x$ and every $0<r<1$,
--   $$
--   0\le\log\frac{\mu(\bar B(x,r))}{\nu(\bar B(x,r))}\le\max\bigl(0,\log M(x)\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean#L206-L221

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

theorem OAI.EntropyRateDimension.BallRatios.logRatio_bounds (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν, ∀ r : ℝ, 0 < r → r < 1 →
      0 ≤ logRatio μ ν x r ∧ logRatio μ ν x r ≤ logEnvelope μ ν x := by sorry
