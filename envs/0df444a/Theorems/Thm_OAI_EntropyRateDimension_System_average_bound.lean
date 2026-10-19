-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_System_average_bound
-- name    : OAI.EntropyRateDimension.System.average_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:41:43.30763+00:00
-- url     : https://prove2.me/theorems/3037ddc5-d34d-4883-ac84-848714d7b828
-- title:
--   Iterated averages preserve uniform bounds
-- statement:
--   Let $f_i$ be affine maps with weights $w_i\ge0$ summing to $1$, and define the averages $A_0f=f$ and $A_{n+1}f(x)=\sum_iw_i\,A_nf(f_i(x))$. If $|f(x)|\le C$ for all $x$, then for all $n$ and $x$,
--   $$
--   |A_nf(x)|\le C .
--   $$
--
--   Each average is a convex combination of values of $f$, so it stays within the same bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/InvariantLaw.lean#L30-L42

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι]

theorem OAI.EntropyRateDimension.System.average_bound (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (n : ℕ) (x : ℝ) : |S.average f n x| ≤ C := by sorry
