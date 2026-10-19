-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_BallRatios_information_component
-- name    : OAI.EntropyRateDimension.BallRatios.information_component
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:47:35.564598+00:00
-- url     : https://prove2.me/theorems/f4860d83-f2a6-4d8f-873d-61a1b8f32f9e
-- title:
--   Ball information under one map of the system
-- statement:
--   Let $\mu$ be a finite self-similar measure, $\mu=\sum_iw_i(f_i)_*\mu$ with $f_i(x)=r_ix+b_i$, and let $\mu_i=w_i(f_i)_*\mu$ be its $i$-th component. For $x$ in the support of $\mu$ and $r>0$, with $I_\mu(x,r)=-\log\mu(\bar B(x,r))$,
--   $$
--   I_\mu\bigl(f_i(x),|r_i|r\bigr)=I_\mu(x,r)-\log w_i-\log\frac{\mu(\bar B(f_i(x),|r_i|r))}{\mu_i(\bar B(f_i(x),|r_i|r))} .
--   $$
--
--   The last term corrects for the other components overlapping the image ball.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallIntegrability.lean#L64-L91

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators

theorem OAI.EntropyRateDimension.BallRatios.information_component {ι : Type uι} [Fintype ι] (S : System ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : S.SelfSimilar μ) (i : ι)
    {x r : ℝ} (hx : x ∈ μ.support) (hr : 0 < r) :
    information μ (S.affine i x) (|S.ratio i| *r) =
      information μ x r - Real.log (S.weight i) -
        logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) := by sorry
