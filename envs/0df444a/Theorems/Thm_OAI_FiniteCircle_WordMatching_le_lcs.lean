-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_le_lcs
-- name    : OAI.FiniteCircle.WordMatching.le_lcs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:24:43.042513+00:00
-- url     : https://prove2.me/theorems/c55ca7ca-2d3f-4012-b5c0-7556c067e529
-- title:
--   A non-crossing matching of $q$ equal letters gives a common subsequence of length $q$
-- statement:
--   Let $x=x_0x_1\cdots x_{m-1}$ and $y=y_0y_1\cdots y_{n-1}$ be words over an alphabet $\alpha$. A word matching of size $q$ between $x$ and $y$ is a pair of strictly increasing maps
--   $$
--   \ell:\{0,\dots,q-1\}\to\{0,\dots,m-1\},\qquad r:\{0,\dots,q-1\}\to\{0,\dots,n-1\}
--   $$
--   with $x_{\ell(k)}=y_{r(k)}$ for every $k<q$: it pairs $q$ positions of $x$ with $q$ positions of $y$ that carry equal letters, without crossings. Let $\operatorname{lcs}(x,y)$ denote the length of a longest common subsequence of $x$ and $y$, a common subsequence being a word obtainable from both $x$ and $y$ by deleting letters (not necessarily contiguous ones).
--
--   **Theorem.** If there is a word matching of size $q$ between $x$ and $y$, then
--   $$
--   q\le\operatorname{lcs}(x,y).
--   $$
--
--   This is the easy half of the correspondence between common subsequences and non-crossing matchings (the development also uses the converse, that a matching of size $\operatorname{lcs}(x,y)$ always exists). It allows one to bound $\operatorname{lcs}(x,y)$ from below, equivalently the deficit $|x|-\operatorname{lcs}(x,y)$ from above, by exhibiting an explicit matching, for instance the restriction of a global matching to a pair of segments.
--
--   **Formalization Note** The matching is the structure `WordMatching x y q`, whose fields `left` and `right` are order embeddings of `Fin q` into the position types `Fin x.length` and `Fin y.length` and whose field `letters` states the equality of matched letters. `lcs x y` is defined as the supremum of the lengths of common sublists.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Matching.lean#L147-L164

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching

open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
variable {α : Type*} {x y : List α} {q : ℕ}

theorem OAI.FiniteCircle.WordMatching.le_lcs (A : WordMatching x y q) : q ≤ lcs x y := by sorry
