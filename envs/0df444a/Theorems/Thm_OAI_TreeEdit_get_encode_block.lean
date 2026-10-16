-- Prove2me | Theorems.Thm_OAI_TreeEdit_get_encode_block
-- name    : OAI.TreeEdit.get_encode_block
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:46:16.113757+00:00
-- url     : https://prove2.me/theorems/65bb3055-ae14-4c58-8ee4-4b742d05aecb
-- title:
--   Position $iP+r$ of a block encoding is letter $r$ of the $i$-th codeword
-- statement:
--   Let $\alpha$ be an alphabet, $P$ a natural number and $c\colon\alpha\to\{0,1\}^P$ a fixed-width binary code, assigning to each symbol $u\in\alpha$ a bit string $c(u)$ of length exactly $P$. For a word $x=(x_0,\dots,x_{\ell-1})$ over $\alpha$ let
--   $\operatorname{enc}_c(x)=c(x_0)\,c(x_1)\cdots c(x_{\ell-1})\in\{0,1\}^{\ell P}$
--   be the concatenation of the codewords of its letters. Indexing letters from $0$, for every $i<\ell$ and every $r<P$
--
--   $$
--   \operatorname{enc}_c(x)_{\,iP+r}=c(x_i)_{\,r}.
--   $$
--
--   Thus the encoding consists of $\ell$ consecutive blocks of length $P$, and the $i$-th block is exactly the codeword of $x_i$. This index formula is the basic bookkeeping fact used to compare windows of encoded words with windows of individual codewords when transferring edit-distance bounds from words over a large alphabet to binary words.
--
--   **Formalization Note** Words are Lean lists; codewords are elements of `Word Bool P` (lists of booleans of length `P`), and `encode c x` is `x.flatMap (fun a => (c a).val)`. The statement uses bounds-checked list indexing; the side conditions $iP+r<\ell P$ and $r<|c(x_i)|$ are proved inside the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/SegmentComparison.lean#L45-L64

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

theorem OAI.TreeEdit.get_encode_block {P : ℕ} (c : α → Word Bool P) (x : List α)
    (i r : ℕ) (hi : i < x.length) (hr : r < P) :
    (encode c x)[i * P + r]'(by
      rw [length_encode]
      have hh := Nat.mul_le_mul_right P (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hh
      omega) = (c x[i]).val[r]'(by rw [(c x[i]).property]; exact hr) := by sorry
