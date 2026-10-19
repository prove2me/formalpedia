-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_BallRatios_logEnvelope_integrable
-- name    : OAI.EntropyRateDimension.BallRatios.logEnvelope_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:44:58.595132+00:00
-- url     : https://prove2.me/theorems/2b6ec55a-0775-4ed0-a2b4-016f2fef73f1
-- title:
--   The log envelope of ball ratios is integrable
-- statement:
--   For measures $\mu,\nu$ on $\mathbb R$, let $M(x)=\sup_q\mu(\bar B(x,q))/\nu(\bar B(x,q))$ over rational radii $0<q\le1$, the log envelope $\max(0,\log M(x))$, and the log ratio $\log\bigl(\mu(\bar B(x,r))/\nu(\bar B(x,r))\bigr)$.
--
--   For finite measures $\mu,\nu$ on $\mathbb R$, the log envelope
--   $$
--   x\mapsto\max\bigl(0,\log M(x)\bigr)
--   $$
--   is integrable with respect to $\nu$.
--
--   This domination lets one pass ball ratios to the limit under integrals along the coding.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean#L150-L167

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

theorem OAI.EntropyRateDimension.BallRatios.logEnvelope_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (logEnvelope μ ν) ν := by sorry
