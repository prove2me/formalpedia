-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_cell_eq_distance_lt
-- name    : OAI.EntropyRateDimension.RandomGrid.cell_eq_distance_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:26:25.792657+00:00
-- url     : https://prove2.me/theorems/9eb653d5-79e7-41f8-9800-e28aac9a5d30
-- title:
--   Points in the same grid cell are closer than the mesh
-- statement:
--   For a mesh $\delta>0$ and a point $u$ of the circle $\mathbb R/\mathbb Z$ with representative $\tilde u\in[0,1)$, let $\mathrm{cell}_{\delta,u}(x)=\lfloor x/\delta+\tilde u\rfloor$. If two points lie in the same cell, they are closer than the mesh:
--   $$
--   \mathrm{cell}_{\delta,u}(x)=\mathrm{cell}_{\delta,u}(y)\ \Longrightarrow\ |x-y|<\delta .
--   $$
--
--   So a fine grid cell has diameter less than its mesh, whatever the random shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean#L39-L52

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
universe uα
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] unitCircleProbability

theorem OAI.EntropyRateDimension.RandomGrid.cell_eq_distance_lt {δ x y : ℝ} (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (h : cell δ u x = cell δ u y) : |x-y| < δ := by sorry
