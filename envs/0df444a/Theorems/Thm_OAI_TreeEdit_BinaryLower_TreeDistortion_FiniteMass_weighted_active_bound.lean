-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_weighted_active_bound
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_active_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:25:06.387588+00:00
-- url     : https://prove2.me/theorems/a37f986c-4ded-4ce7-8721-584188cb78f1
-- title:
--   Weighted mass of active indices
-- statement:
--   Let $\iota$ be finite and $H,w\ge0$, $\mu\le4$ on $\iota$, with $\mu_i=0$ unless $i$ is active. Let $K>0$ and suppose every active, non-exceptional $i$ has $w_i\ge K$. Suppose also
--   $$
--   2\sum_iw_iH_i\le M\qquad\text{and}\qquad\sum_{i\text{ exceptional}}H_i\le\varepsilon .
--   $$
--   Then $\sum_i\mu_iH_i\le4\bigl(\varepsilon+M/(2K)\bigr)$.
--
--   Mass is either exceptional or carried by indices of large weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L53-L92

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_active_bound {ι : Type*} [Fintype ι]
    (H w μ : ι → ℝ) (active exceptional : ι → Prop)
    (M ε K : ℝ) (hK : 0 < K)
    (hH : ∀ i, 0 ≤ H i) (hw : ∀ i, 0 ≤ w i)
    (hμ : ∀ i, μ i ≤ 4)
    (hzero : ∀ i, ¬ active i → μ i = 0)
    (hdense : ∀ i, active i → ¬ exceptional i → K ≤ w i)
    (hleaf : 2 * ∑ i, w i * H i ≤ M)
    (hexceptional : (∑ i, if exceptional i then H i else 0) ≤ ε) :
    (∑ i, μ i * H i) ≤ 4 * (ε + M / (2 * K)) := by sorry
