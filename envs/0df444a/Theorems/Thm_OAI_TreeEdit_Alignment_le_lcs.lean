-- Prove2me | Theorems.Thm_OAI_TreeEdit_Alignment_le_lcs
-- name    : OAI.TreeEdit.Alignment.le_lcs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:45:07.852982+00:00
-- url     : https://prove2.me/theorems/1b51bf1b-c8dd-463b-91c3-9273f12face9
-- title:
--   An alignment of $n$ matched positions gives a common subsequence of length $n$
-- statement:
--   Let $x=(x_0,\dots,x_{|x|-1})$ and $y=(y_0,\dots,y_{|y|-1})$ be finite words over an alphabet $\alpha$, and let $\operatorname{lcs}(x,y)$ be the length of a longest common subsequence of $x$ and $y$ (a subsequence of $x$ is a word obtained from $x$ by deleting some of its letters). An *alignment of size $n$* between $x$ and $y$ is a pair of strictly increasing maps $\lambda\colon\{0,\dots,n-1\}\to\{0,\dots,|x|-1\}$ and $\rho\colon\{0,\dots,n-1\}\to\{0,\dots,|y|-1\}$ such that $x_{\lambda(i)}=y_{\rho(i)}$ for every $i<n$. If an alignment of size $n$ exists, then
--
--   $$
--   n\le\operatorname{lcs}(x,y).
--   $$
--
--   Alignments are the combinatorial certificates used throughout the edit-distance lower bound to bound longest common subsequences from below, and hence the deficit $|x|-\operatorname{lcs}(x,y)$ from above. The converse direction, that a longest common subsequence yields an alignment of size $\operatorname{lcs}(x,y)$, is a separate statement.
--
--   **Formalization Note** An alignment is the structure `Alignment x y n` with fields `left : Fin n ↪o Fin x.length`, `right : Fin n ↪o Fin y.length` (order embeddings) and the agreement condition `x.get (left i) = y.get (right i)`. `lcs x y` is defined as the supremum of the lengths of common sublists (`List.Sublist`) of `x` and `y`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Alignments.lean#L20-L33

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments

open OAI OAI.TreeEdit OAI.TreeEdit.Alignment
universe u
variable {α : Type u} {x y z : List α}
variable {n : ℕ}

theorem OAI.TreeEdit.Alignment.le_lcs (a : Alignment x y n) : n ≤ lcs x y := by sorry
