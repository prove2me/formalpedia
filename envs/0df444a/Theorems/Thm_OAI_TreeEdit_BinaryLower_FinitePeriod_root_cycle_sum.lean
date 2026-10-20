-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FinitePeriod_root_cycle_sum
-- name    : OAI.TreeEdit.BinaryLower.FinitePeriod.root_cycle_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:48:28.178399+00:00
-- url     : https://prove2.me/theorems/c5ed0c6c-3df2-490e-ba26-06d71f7d63c0
-- title:
--   Cycle sums for a nontrivial root of unity
-- statement:
--   Let $z\in\mathbb C$ with $|z|=1$, $z\ne1$ and $z^q=1$. Then
--   $$
--   \sum_{s=0}^{q-1}\bigl|1-z^{s+1}\bigr|^2=2q .
--   $$
--
--   Averaged over a full cycle, a nontrivial root of unity has multiplier exactly $2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FinitePeriod.lean#L65-L81

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.FinitePeriod.root_cycle_sum {z : ℂ} {q : ℕ} (hz : ‖z‖ = 1)
    (hne : z ≠ 1) (hroot : z ^ q = 1) :
    ∑ s ∈ Finset.range q, ‖1 - z ^ (s + 1)‖ ^ 2 = 2 * (q : ℝ) := by sorry
