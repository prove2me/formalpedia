-- Prove2me | Theorems.Thm_OAI_TreeEdit_card_block_fiber
-- name    : OAI.TreeEdit.card_block_fiber
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:48:23.661479+00:00
-- url     : https://prove2.me/theorems/1b8c3df5-71ea-4238-b3f7-3506e600c6ca
-- title:
--   An increasing index map sends at most $P$ indices into any block of length $P$
-- statement:
--   Let $M,P,N$ be natural numbers with $P>0$. Partition the positions $\{0,1,\dots,MP-1\}$ into $M$ consecutive blocks of length $P$, the block of position $q$ being $\lfloor q/P\rfloor\in\{0,\dots,M-1\}$. Let $f\colon\{0,\dots,N-1\}\to\{0,\dots,MP-1\}$ be strictly increasing. Then for every block $a\in\{0,\dots,M-1\}$
--
--   $$
--   \#\bigl\{\,i\in\{0,\dots,N-1\}:\ \lfloor f(i)/P\rfloor=a\,\bigr\}\le P.
--   $$
--
--   In words, one side of an alignment cannot use more positions of a block than the block has. Consequently the numbers $P-\#\{i:\lfloor f(i)/P\rfloor=a\}$ are genuine (nonnegative) losses, and summed over the blocks they count exactly the $MP-N$ positions of a word of length $MP$ that an alignment of size $N$ leaves unmatched.
--
--   **Formalization Note** $f$ is an order embedding `Fin N ↪o Fin (M * P)`, and the block of a position is `blockIndex hP q`, the element `q / P` of `Fin M` (natural-number division).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CycleCharging.lean#L87-L106

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison

open OAI OAI.TreeEdit
universe u
attribute [local instance] Classical.propDecidable

theorem OAI.TreeEdit.card_block_fiber {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) (a : Fin M) :
    (Finset.univ.filter (fun i => blockIndex hP (f i) = a)).card ≤ P := by sorry
