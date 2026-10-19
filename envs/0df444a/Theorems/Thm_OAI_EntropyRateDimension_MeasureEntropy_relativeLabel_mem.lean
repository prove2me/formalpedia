-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_relativeLabel_mem
-- name    : OAI.EntropyRateDimension.MeasureEntropy.relativeLabel_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:10:26.703712+00:00
-- url     : https://prove2.me/theorems/c8dd7626-1476-4bc7-b69b-a9486c94653b
-- title:
--   Relative labels of a fine cell inside a coarse cell
-- statement:
--   For meshes $s,t>0$ and shifts $u,v$, let $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, and define the relative label
--   $$
--   \rho(x)=\ell_{s,u}(x)-\Bigl\lfloor\frac ts\,\ell_{t,v}(x)+u-\frac ts\,v\Bigr\rfloor .
--   $$
--   Then $\rho(x)\in\{0,1,\dots,\lceil t/s\rceil\}$ for every $x$.
--
--   So the $s$-cell of $x$ is determined by its $t$-cell and one of $\lceil t/s\rceil+1$ values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L471-L484

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

theorem OAI.EntropyRateDimension.MeasureEntropy.relativeLabel_mem {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v x : ℝ) :
    relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ := by sorry
