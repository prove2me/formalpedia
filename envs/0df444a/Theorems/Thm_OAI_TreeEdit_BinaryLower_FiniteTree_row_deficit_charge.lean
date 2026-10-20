-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_row_deficit_charge
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.row_deficit_charge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:09:46.347769+00:00
-- url     : https://prove2.me/theorems/839c4943-d181-4134-bcc6-e70e89bae1d8
-- title:
--   Charging a deficit to half of the children
-- statement:
--   Let $\delta_1,\dots,\delta_m\ge0$, $q\ge0$, and let $\mathrm{bad}\subseteq\{1..m\}$ satisfy $\delta_i\ge q$ for $i\in\mathrm{bad}$ and $m\le2|\mathrm{bad}|$. Then
--   $$
--   \frac{m\,q}2\le\sum_{i=1}^m\delta_i .
--   $$
--
--   If at least half of the children each lose $q$, the total loss is at least $mq/2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteSeparationArithmetic.lean#L13-L29

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree

theorem OAI.TreeEdit.BinaryLower.FiniteTree.row_deficit_charge {m : ℕ} (bad : Finset (Fin m))
    (δ : Fin m → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hnonneg : ∀ i, 0 ≤ δ i) (hbad : ∀ i ∈ bad, q ≤ δ i)
    (hhalf : m ≤ 2 * bad.card) :
    (m : ℝ) * q / 2 ≤ ∑ i, δ i := by sorry
