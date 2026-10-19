-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Interpolation_tendsto_div_of_bounded_gaps
-- name    : OAI.EntropyRateDimension.Interpolation.tendsto_div_of_bounded_gaps
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:52:16.748673+00:00
-- url     : https://prove2.me/theorems/9492b203-8e28-4279-898f-ef50885e8ea3
-- title:
--   From a sequence of times with bounded gaps to all times
-- statement:
--   Let $F:\mathbb R\to\mathbb R$ be nondecreasing and $t_n$ a nondecreasing sequence with $t_0=0$, $t_{n+1}\le t_n+C$ and $t_n\to\infty$. If
--   $$
--   \lim_{n\to\infty}\frac{F(t_n)}{t_n}=d,
--   $$
--   then $F(s)/s\to d$ as $s\to\infty$.
--
--   It converts limits along the coding radii into limits along all radii.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Interpolation.lean#L22-L103

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth

open OAI OAI.EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology

theorem OAI.EntropyRateDimension.Interpolation.tendsto_div_of_bounded_gaps {F : ℝ → ℝ} {t : ℕ → ℝ} {C d : ℝ}
    (hF : Monotone F) (ht : Monotone t) (ht0 : t 0 = 0)
    (hstep : ∀ n, t (n+1) ≤ t n+C) (htop : Tendsto t atTop atTop)
    (hlim : Tendsto (fun n => F (t n) / t n) atTop (𝓝 d)) :
    Tendsto (fun s => F s / s) atTop (𝓝 d) := by sorry
