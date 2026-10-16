-- Prove2me | Theorems.Thm_OAI_TreeEdit_Words_cycles_deficit
-- name    : OAI.TreeEdit.Words.cycles_deficit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:50:13.693145+00:00
-- url     : https://prove2.me/theorems/64e58742-01ab-473c-a774-7dd8def9bc86
-- title:
--   Cyclic interleavings of block words have deficit at least $T\delta/2$ when every pairing of cycles loses $\delta$
-- statement:
--   Let $m\ge2$, $B\ge1$ and $T$ be natural numbers and let $\beta_0,\dots,\beta_{m-1}$ be alphabets. Let $x=(x_{a,i})$ and $y=(y_{a,i})$ be two arrays of blocks indexed by $a\in\{0,\dots,T-1\}$ and $i\in\{0,\dots,m-1\}$, where $x_{a,i}$ and $y_{a,i}$ are words of length $B$ over $\beta_i$. The *cyclic interleaving* $\operatorname{cyc}(x)$ is the word of length $TmB$ over the disjoint union $\bigsqcup_{i}\beta_i$ whose letter at position $a\,mB+i\,B+q$ (with $a<T$, $i<m$, $q<B$) is the letter $(x_{a,i})_q$ tagged with its colour $i$. Thus $\operatorname{cyc}(x)$ consists of $T$ cycles, the $a$-th cycle being the concatenation of the tagged blocks $x_{a,0},\dots,x_{a,m-1}$.
--
--   For words $u,v$ let $\operatorname{lcs}(u,v)$ be the length of a longest common subsequence and $\operatorname{def}(u,v)=|u|-\operatorname{lcs}(u,v)$ the deficit. Let $\delta$ be a real number with $\delta\le(m-2)B$, and assume that every cycle of $x$ compared with every cycle of $y$ has total blockwise deficit at least $\delta$:
--   $$\delta\le\sum_{i=0}^{m-1}\operatorname{def}(x_{a,i},y_{b,i})\qquad\text{for all } a,b\in\{0,\dots,T-1\}.$$
--   Then
--
--   $$
--   T\,\delta\le 2\,\operatorname{def}\bigl(\operatorname{cyc}(x),\operatorname{cyc}(y)\bigr).
--   $$
--
--   So a deficit of $\delta$ for every pair of cycles forces a deficit of at least $T\delta/2$ for the interleaved words, however a longest common subsequence distributes the cycles. This is the step that propagates edit-distance separation from one level of the tree words to the next.
--
--   **Formalization Note** Blocks are elements of `Word (β i) B` (lists of length $B$); the interleaving is `Words.cycles x : Word (Sigma β) (T * (m * B))`, defined positionwise through `Fin.divNat` and `Fin.modNat`. `deficit u v` is `u.length - lcs u v` (natural subtraction, which does not truncate because $\operatorname{lcs}(u,v)\le|u|$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CyclicWords.lean#L121-L156

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords

open OAI OAI.TreeEdit OAI.TreeEdit.Words
universe u
attribute [local instance] Classical.propDecidable
variable {β : Type*} {n : ℕ}

theorem OAI.TreeEdit.Words.cycles_deficit {m T B : ℕ} {β : Fin m → Type*} (hm : 2 ≤ m) (hB : 0 < B)
    (x y : Fin T → ∀ i, Word (β i) B) (δ : ℝ)
    (hδ : δ ≤ ((m - 2) * B : ℕ))
    (hblocks : ∀ a b, δ ≤ ∑ i : Fin m, (deficit (x a i).val (y b i).val : ℝ)) :
    (T : ℝ) * δ ≤ 2 * (deficit (cycles x).val (cycles y).val : ℝ) := by sorry
