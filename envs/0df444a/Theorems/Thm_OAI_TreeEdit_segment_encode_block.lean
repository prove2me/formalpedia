-- Prove2me | Theorems.Thm_OAI_TreeEdit_segment_encode_block
-- name    : OAI.TreeEdit.segment_encode_block
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:46:49.159513+00:00
-- url     : https://prove2.me/theorems/97b78257-b37b-4163-b25c-fdc32a8489e8
-- title:
--   A window inside one block of a block encoding is the corresponding window of that codeword
-- statement:
--   For a word $w=(w_0,\dots,w_{N-1})$ and natural numbers $b,\ell$ let $w[b;\ell]$ denote the *segment* of $w$ obtained by discarding the first $b$ letters and keeping the next $\ell$ letters (fewer if the word ends earlier); when $b+\ell\le N$ this is $(w_b,w_{b+1},\dots,w_{b+\ell-1})$.
--
--   Let $c\colon\alpha\to\{0,1\}^P$ be a fixed-width binary code, so each $c(u)$ is a bit string of length $P$, and for a word $x=(x_0,\dots,x_{|x|-1})$ over $\alpha$ let $\operatorname{enc}_c(x)=c(x_0)\,c(x_1)\cdots c(x_{|x|-1})$ be the concatenation of its codewords. If $i<|x|$ and $b+\ell\le P$, then
--
--   $$
--   \operatorname{enc}_c(x)\,[\,iP+b;\ \ell\,]=c(x_i)\,[\,b;\ \ell\,].
--   $$
--
--   So a window of the encoding that lies inside its $i$-th block is literally a window of the single codeword $c(x_i)$. This lets an aligned stretch of an encoded word that stays inside one block be compared directly with a stretch of a codeword.
--
--   **Formalization Note** `segment w b ℓ` is defined as `(w.drop b).take ℓ`; codewords are elements of `Word Bool P` and `encode c x` is `x.flatMap (fun a => (c a).val)`. Positions are $0$-indexed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/SegmentComparison.lean#L66-L80

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison

open OAI OAI.TreeEdit
universe u
variable {α : Type u} {x y z : List α}

theorem OAI.TreeEdit.segment_encode_block {P : ℕ} (c : α → Word Bool P) (x : List α)
    (i start len : ℕ) (hi : i < x.length) (hseg : start + len ≤ P) :
    segment (encode c x) (i * P + start) len = segment (c x[i]).val start len := by sorry
