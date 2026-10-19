-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_ScalarEntropy_weighted_negMulLog_le
-- name    : OAI.ThresholdParallelRepetition.ScalarEntropy.weighted_negMulLog_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:58:42.503209+00:00
-- url     : https://prove2.me/theorems/bc14db8c-9b9d-433d-b3dc-00478a375ccf
-- title:
--   Weighted entropy bound $\sum_i w_i\,\eta(t_i)\le p\log(d/p)$ under a mass constraint
-- statement:
--   Let $\eta(t)=-t\log t$ for $t\ge0$ (with $\eta(0)=0$). Let $\iota$ be a finite index set, let $w_i\ge0$ and $t_i\ge0$ for $i\in\iota$, and let $d>0$ and $p>0$ be real numbers with
--   $$\sum_iw_i\le d\qquad\text{and}\qquad\sum_iw_it_i=p .$$
--   Then
--
--   $$
--   \sum_{i\in\iota}w_i\,\eta(t_i)\;\le\;p\log\frac dp .
--   $$
--
--   For $w_i\equiv1$ on a set of $d$ elements this is the familiar bound that a nonnegative vector of total mass $p$ spread over $d$ points satisfies $\sum_i-t_i\log t_i\le p\log(d/p)$. The weighted form is used to bound averaged entropic potentials whose total weight is controlled.
--
--   **Formalization Note** $\eta$ is `Real.negMulLog`; the hypotheses are `0 < d`, `∑ i, w i ≤ d`, `0 < p` and `∑ i, w i * t i = p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/RelativeEntropy.lean#L47-L68

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy

open OAI OAI.ThresholdParallelRepetition
universe u_ι u_α u_β u_n u_m
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.ThresholdParallelRepetition.ScalarEntropy.weighted_negMulLog_le {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 ≤ t i)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ i, w i ≤ d) (hp : 0 < p)
    (hm : ∑ i, w i*t i = p) :
    (∑ i, w i*Real.negMulLog (t i)) ≤ p*Real.log (d/p) := by sorry
