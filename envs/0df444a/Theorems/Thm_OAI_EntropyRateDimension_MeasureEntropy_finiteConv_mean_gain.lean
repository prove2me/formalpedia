-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_finiteConv_mean_gain
-- name    : OAI.EntropyRateDimension.MeasureEntropy.finiteConv_mean_gain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:55:40.39671+00:00
-- url     : https://prove2.me/theorems/ef78adcf-1e0a-4fc2-85d7-6b593027535c
-- title:
--   Entropy gain of a finite convolution, averaged over components
-- statement:
--   Let $\bar H_s$ denote the averaged grid entropy, $\mathrm{W}(\lambda)=\bar H_s(\lambda)-\bar H_{Ns}(\lambda)$ the window between scales $s$ and $Ns$, and $\mathrm{def}_\mu(v)=\log2-(\bar H_v(\mu)-\bar H_{2v}(\mu))$. Let $\mu$ be compactly carried with $\mathrm{def}_\mu(v)\ge\delta$ for all $v>0$. Let $b\ne0$, and suppose the image of $\mu$ under $x\mapsto bx$ is a mixture $\sum_zp_z\tau_z$ of compactly carried probability measures. Let $\nu$ be a finite law, $a\in\mathbb R$, and $\ell$ a band such that every edge $(x,y)$ of $\nu$ in band $\ell$ has $s<|a(y-x)|<Ns$ and error $(s/|a(y-x)|+|a(y-x)|/(Ns))\log2\le\eta$. Then
--   $$
--   (\delta-\eta)\,\mathrm{cap}(\nu,\ell)\le\sum_zp_z\Bigl(\mathrm{W}\bigl(\textstyle\sum_x\nu(x)\tau_z(\cdot-ax)\bigr)-\mathrm{W}(\tau_z)\Bigr).
--   $$
--
--   So a law with large capacity in a band, convolved at the right scale with pieces of a measure that never saturates, raises the entropy window in proportion to that capacity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/PairGain.lean#L258-L306

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ
open MeasureTheory FairPairs
open scoped BigOperators ENNReal

theorem OAI.EntropyRateDimension.MeasureEntropy.finiteConv_mean_gain {β : Type uβ} [Fintype β]
    (ν : FairPairs.Law) (a b : ℝ) (hb : b ≠ 0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (τ : β → Measure ℝ) [∀ z, IsProbabilityMeasure (τ z)]
    (hτ : ∀ z, CompactlyCarried (τ z))
    (p : β → ℝ) (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z=1)
    (hm : μ.map (fun x => b*x) = ∑ z, ENNReal.ofReal (p z) • τ z)
    {δ η s : ℝ} (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) (ℓ : ℤ)
    (hv : ∀ e : ν.edges ℓ, s < |a*e.val.2-a*e.val.1| ∧ |a*e.val.2-a*e.val.1| < N*s)
    (herr : ∀ e : ν.edges ℓ,
      (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2 ≤ η) :
    (δ-η)*FairPairs.capacity ν ℓ ≤
      ∑ z, p z*(window (finiteConv ν a (τ z)) s (N*s)-window (τ z) s (N*s)) := by sorry
