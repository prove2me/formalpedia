-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_tail_append
-- name    : OAI.EntropyRateDimension.Typed.tail_append
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:57:07.922743+00:00
-- url     : https://prove2.me/theorems/19ba3ebb-aa70-47d0-8616-67f6be571458
-- title:
--   Tail measures compose along concatenated words
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$. For a word $w=w_0\cdots w_{n-1}$ write $f_w=f_{w_0}\circ\cdots\circ f_{w_{n-1}}$, $f_w(x)=a_wx+b_w$, and $w(w)=\prod_jw_{w_j}$. Fix a tag map on letters. The typed law $\nu_w$ of a word $w$ is the law of the offset $b_v$ for a random word $v$ with the same tags as $w$, drawn with probability proportional to $w(v)$. Its Shannon entropy and its entropy on the grid of mesh $\rho$ are measured in bits. The tail measure of $w$ applied to a measure $\mu$ is $\mathrm{tail}_w(\mu)=\sum_vP(v\mid w)\,(f_v)_*\mu$, summed over words $v$ with the tags of $w$.
--
--   For words $w$ of length $m$ and $z$ of length $n$, and any measure $\mu$,
--   $$
--   \mathrm{tail}_{wz}(\mu)=\mathrm{tail}_w\bigl(\mathrm{tail}_z(\mu)\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/TypedLaw.lean#L155-L168

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uι uα uβ uγ uM
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem OAI.EntropyRateDimension.Typed.tail_append (S : System α) (tag : α → β) (μ : Measure ℝ)
    {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    tail S tag μ (Fin.append w z)=tail S tag (tail S tag μ z) w := by sorry
