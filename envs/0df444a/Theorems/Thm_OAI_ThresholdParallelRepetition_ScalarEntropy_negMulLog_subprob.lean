-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_ScalarEntropy_negMulLog_subprob
-- name    : OAI.ThresholdParallelRepetition.ScalarEntropy.negMulLog_subprob
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:58:11.182297+00:00
-- url     : https://prove2.me/theorems/cc129c51-c021-4886-a493-91cfacbe3367
-- title:
--   Jensen's inequality for $-t\log t$ with sub-probability weights
-- statement:
--   Let $\eta:[0,\infty)\to\mathbb{R}$ be the entropy function $\eta(t)=-t\log t$, with $\eta(0)=0$. Let $\iota$ be a finite index set, let $(w_i)_{i\in\iota}$ be weights with $w_i\ge0$ and $\sum_iw_i\le1$, and let $(t_i)_{i\in\iota}$ be points with $t_i\ge0$. Then
--
--   $$
--   \sum_{i\in\iota}w_i\,\eta(t_i)\;\le\;\eta\Bigl(\sum_{i\in\iota}w_i\,t_i\Bigr).
--   $$
--
--   This is Jensen's inequality for the concave function $\eta$, extended from probability weights to sub-probability weights; the extension is possible because $\eta(0)=0$. It is the scalar inequality behind entropy bounds for spectral decompositions and measurement statistics with subnormalized weights.
--
--   **Formalization Note** $\eta$ is `Real.negMulLog`, defined on all of $\mathbb{R}$ as $-t\log t$ with Lean's $\log0=0$, so $\eta(0)=0$; only its values on $[0,\infty)$ enter here. The index type $\iota$ may be empty, in which case both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/RelativeEntropy.lean#L13-L30

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

theorem OAI.ThresholdParallelRepetition.ScalarEntropy.negMulLog_subprob {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1)
    (ht : ∀ i, 0 ≤ t i) :
    (∑ i, w i * Real.negMulLog (t i)) ≤ Real.negMulLog (∑ i, w i*t i) := by sorry
