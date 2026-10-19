-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_sourceBlock_card_le
-- name    : OAI.FiniteCircle.WordMatching.sourceBlock_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:25:20.191986+00:00
-- url     : https://prove2.me/theorems/1658b508-8d3c-47f9-b08a-ef9e3f154c6e
-- title:
--   A block of $w$ consecutive positions of the source word carries at most $w$ matched pairs
-- statement:
--   Let $x=x_0x_1\cdots x_{m-1}$ and $y=y_0y_1\cdots y_{n-1}$ be words over an alphabet $\alpha$. A word matching of size $q$ between $x$ and $y$ is a pair of strictly increasing maps
--   $$
--   \ell:\{0,\dots,q-1\}\to\{0,\dots,m-1\},\qquad r:\{0,\dots,q-1\}\to\{0,\dots,n-1\}
--   $$
--   with $x_{\ell(k)}=y_{r(k)}$ for every $k<q$: it pairs $q$ positions of $x$ with $q$ positions of $y$ that carry equal letters, without crossings. For a block length $w\ge1$ and an index $i\in\mathbb{N}$, the source block of the matching is
--   $$
--   S_i=\bigl\{k<q:\ \lfloor \ell(k)/w\rfloor=i\bigr\},
--   $$
--   the set of matched pairs whose position in $x$ lies in the $i$-th block $\{iw,iw+1,\dots,iw+w-1\}$ of $x$.
--
--   **Theorem.** For every $w>0$ and every $i\in\mathbb{N}$,
--   $$
--   |S_i|\le w .
--   $$
--
--   When the source word is cut into rows of length $w$, the number $w-|S_i|$ counts the unmatched positions of row $i$ (the source loss of that row). This lemma shows that this count is never truncated, so that summing it over all rows gives exactly $|x|-q$; this is the bookkeeping behind row-by-row lower bounds for the deficit $|x|-\operatorname{lcs}(x,y)$.
--
--   **Formalization Note** In Lean the matching is `WordMatching x y q` (order embeddings `left`, `right` and the field `letters`), and the source block is the finset `A.sourceBlock w i` of indices `k : Fin q` with `(A.left k).val / w = i`. The index `i` is an arbitrary natural number; blocks beyond the end of `x` are empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Matching.lean#L230-L246

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching

open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
variable {α : Type*} {x y : List α} {q : ℕ}

theorem OAI.FiniteCircle.WordMatching.sourceBlock_card_le (A : WordMatching x y q) {w : ℕ} (hw : 0 < w) (i : ℕ) :
    (A.sourceBlock w i).card ≤ w := by sorry
