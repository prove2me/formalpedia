-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
-- name    : OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.map_affine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:09:21.908023+00:00
-- url     : https://prove2.me/theorems/006ee926-5967-41fc-9fd0-1b551b8bf022
-- title:
--   Affine images of compactly carried measures
-- statement:
--   Let $\mu$ be a measure on $\mathbb R$ that vanishes outside some interval $[-B,B]$. For all real $a,b$, the image of $\mu$ under $x\mapsto ax+b$ also vanishes outside a bounded interval:
--   $$
--   \mu\bigl\{x:|ax+b|>|a|B+|b|\bigr\}=0 .
--   $$
--
--   So compact carriers are preserved by affine maps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L383-L396

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.map_affine {μ : Measure ℝ} (hμ : CompactlyCarried μ) (a b : ℝ) :
    CompactlyCarried (μ.map (fun x => a*x+b)) := by sorry
