-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_BallRatios_ae_logRatio_limit
-- name    : OAI.EntropyRateDimension.BallRatios.ae_logRatio_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:46:28.176883+00:00
-- url     : https://prove2.me/theorems/ef55312f-e6ed-4386-8c25-fa83b835b255
-- title:
--   Log ball ratios converge to the log density
-- statement:
--   For measures $\mu,\nu$ on $\mathbb R$, let $M(x)=\sup_q\mu(\bar B(x,q))/\nu(\bar B(x,q))$ over rational radii $0<q\le1$, the log envelope $\max(0,\log M(x))$, and the log ratio $\log\bigl(\mu(\bar B(x,r))/\nu(\bar B(x,r))\bigr)$.
--
--   Let $\mu,\nu$ be finite measures on $\mathbb R$ with $\nu\le\mu$. For $\nu$-almost every $x$, the Radon–Nikodym derivative satisfies $\frac{d\mu}{d\nu}(x)\ge1$, and
--   $$
--   \lim_{r\to0^+}\log\frac{\mu(\bar B(x,r))}{\nu(\bar B(x,r))}=\log\frac{d\mu}{d\nu}(x).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean#L223-L239

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

theorem OAI.EntropyRateDimension.BallRatios.ae_logRatio_limit (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν,
      1 ≤ (μ.rnDeriv ν x).toReal ∧
      Tendsto (logRatio μ ν x) (𝓝[>] 0) (𝓝 (Real.log (μ.rnDeriv ν x).toReal)) := by sorry
