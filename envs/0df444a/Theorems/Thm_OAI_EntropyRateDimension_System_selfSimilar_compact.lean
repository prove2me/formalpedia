-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_compact
-- name    : OAI.EntropyRateDimension.System.selfSimilar_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T03:58:23.586743+00:00
-- url     : https://prove2.me/theorems/96df8a71-5c3d-4d9f-9aca-57cdab0543e7
-- title:
--   Self-similar measures have bounded support
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be finitely many affine maps of $\mathbb R$ with $|r_i|<1$, with positive weights summing to $1$, and let $\mu$ be a probability measure with $\mu=\sum_iw_i(f_i)_*\mu$. Then $\mu$ is carried by a bounded interval:
--   $$
--   \exists B>0:\qquad \mu\bigl(\mathbb R\setminus[-B,B]\bigr)=0 .
--   $$
--
--   No compactness of the support is assumed in advance; it follows from the self-similarity equation alone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Basic.lean#L124-L190

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem OAI.EntropyRateDimension.System.selfSimilar_compact (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : ∃ B : ℝ, 0 < B ∧ μ (Set.Icc (-B) B)ᶜ = 0 := by sorry
