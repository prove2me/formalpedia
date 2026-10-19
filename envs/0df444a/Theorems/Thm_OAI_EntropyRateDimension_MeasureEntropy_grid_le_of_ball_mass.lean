-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_grid_le_of_ball_mass
-- name    : OAI.EntropyRateDimension.MeasureEntropy.grid_le_of_ball_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:35:33.550034+00:00
-- url     : https://prove2.me/theorems/69bcf868-34a5-430a-a3ae-a0f0900793e0
-- title:
--   Grid entropy bounded by ball masses on a large set
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ carried by $[-B,B]$, $s>0$, $u\in[0,1]$, $q>0$, and let $E$ be a set with $\mu(E^c)\le\eta$ such that every $x\in E$ has $\mu(B(x,s/2))\ge q$. Let $H_{s,u}(\mu)$ be the entropy of the grid label $\lfloor x/s+u\rfloor$. Then
--   $$
--   H_{s,u}(\mu)\le\log2+\log\max\Bigl(1,\frac3q\Bigr)+\eta\log\max\bigl(1,N\bigr),
--   $$
--   where $N$ is the number of integers in $[\lfloor-B/s\rfloor,\lfloor B/s+1\rfloor]$.
--
--   So if most points carry a ball of mass $q$ at scale $s$, the grid entropy is about $\log(1/q)$ up to an error controlled by $\eta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/LocalEntropy.lean#L178-L209

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.MeasureEntropy.grid_le_of_ball_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u q η : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, q ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 2+Real.log (max 1 (3/q))+
      η*Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) := by sorry
