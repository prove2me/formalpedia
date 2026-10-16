-- Prove2me | Theorems.Thm_OAI_TreeEdit_Words_cycles_val
-- name    : OAI.TreeEdit.Words.cycles_val
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:54:43.764995+00:00
-- url     : https://prove2.me/theorems/0dcf9c8e-79d1-42ba-8040-d7946806f0d9
-- title:
--   The cyclic interleaving of a block array is the concatenation of its colour-tagged blocks
-- statement:
--   Let $m,T,B$ be natural numbers and $\beta_0,\dots,\beta_{m-1}$ alphabets, and let $x=(x_{a,i})$ be an array of blocks indexed by $a\in\{0,\dots,T-1\}$ and $i\in\{0,\dots,m-1\}$, where $x_{a,i}$ is a word of length $B$ over $\beta_i$. The *cyclic interleaving* $\operatorname{cyc}(x)$ is defined positionwise as the word of length $TmB$ over the disjoint union $\bigsqcup_i\beta_i$ whose letter at position $r<TmB$ is
--   $$\bigl(i,\ (x_{a,i})_q\bigr),\qquad a=\Bigl\lfloor\frac{r}{mB}\Bigr\rfloor,\quad i=\Bigl\lfloor\frac{r\bmod mB}{B}\Bigr\rfloor,\quad q=(r\bmod mB)\bmod B.$$
--   For a word $w=(w_0,\dots,w_{B-1})$ over $\beta_i$ let $\iota_i(w)=((i,w_0),\dots,(i,w_{B-1}))$ be $w$ with every letter tagged by $i$. Then
--
--   $$
--   \operatorname{cyc}(x)=\prod_{a=0}^{T-1}\ \prod_{i=0}^{m-1}\ \iota_i(x_{a,i}),
--   $$
--
--   where the products denote concatenation in increasing order of the index.
--
--   So $\operatorname{cyc}(x)$ is the concatenation of $T$ cycles, the $a$-th cycle being the tagged blocks $x_{a,0},x_{a,1},\dots,x_{a,m-1}$ in order. This converts the positional definition into a concatenation, which is what allows edit-distance bounds for concatenations to be applied block by block (for instance the upper bound $\operatorname{ed}(\operatorname{cyc}(x),\operatorname{cyc}(y))\le\sum_{a,i}\operatorname{ed}(x_{a,i},y_{a,i})$, where $\operatorname{ed}$ is the edit distance: the least number of single-letter insertions, deletions and substitutions turning one word into the other).
--
--   **Formalization Note** Blocks are elements of `Word (β i) B`; `Words.cycles x` is `Words.ofFn` of the positional formula, written with `Fin.divNat` and `Fin.modNat` on `Fin (T * (m * B))`. The right-hand side is `List.flatten` of `List.ofFn`, and the tagging is `List.map (Sigma.mk i)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/WordOperations.lean#L53-L94

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation

open OAI OAI.TreeEdit OAI.TreeEdit.Words
universe u v
variable {α : Type u} {x y z : List α}
attribute [local instance] Classical.propDecidable
variable {β : Type v} {n : ℕ}

theorem OAI.TreeEdit.Words.cycles_val {m T B : ℕ} {β : Fin m → Type*}
    (x : Fin T → ∀ i, Word (β i) B) :
    (cycles x).val = (List.ofFn fun a =>
      (List.ofFn fun i => ((x a i).val.map (Sigma.mk i))).flatten).flatten := by sorry
