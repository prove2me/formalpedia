-- Prove2me | Theorems.Thm_OAI_TreeEdit_span_card_le_lcs
-- name    : OAI.TreeEdit.span_card_le_lcs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:47:13.754516+00:00
-- url     : https://prove2.me/theorems/cdb350c8-4567-4ebc-b052-346dda418d09
-- title:
--   Part of an alignment is bounded by the longest common subsequence of the windows it spans
-- statement:
--   Let $x$ and $y$ be finite words over an alphabet $\beta$, and let $f\colon\{0,\dots,N-1\}\to\{0,\dots,|x|-1\}$ and $g\colon\{0,\dots,N-1\}\to\{0,\dots,|y|-1\}$ be strictly increasing maps with $x_{f(i)}=y_{g(i)}$ for all $i<N$, i.e. an alignment of size $N$ between $x$ and $y$. Let $S\subseteq\{0,\dots,N-1\}$ be nonempty, with least element $i_{\min}$ and greatest element $i_{\max}$. The part of the alignment indexed by $S$ uses positions of $x$ in the interval $[f(i_{\min}),f(i_{\max})]$, which has $\ell_f=f(i_{\max})-f(i_{\min})+1$ positions, and positions of $y$ in $[g(i_{\min}),g(i_{\max})]$, which has $\ell_g=g(i_{\max})-g(i_{\min})+1$ positions. Then
--
--   $$
--   |S|\le\operatorname{lcs}\Bigl(x\,[\,f(i_{\min});\ \ell_f\,],\ \ y\,[\,g(i_{\min});\ \ell_g\,]\Bigr),
--   $$
--
--   where $w[b;\ell]=(w_b,\dots,w_{b+\ell-1})$ is the segment of $w$ of length $\ell$ starting at position $b$, and $\operatorname{lcs}(u,v)$ is the length of a longest common subsequence of $u$ and $v$.
--
--   Thus every part of an alignment is witnessed inside the windows it spans. This localizes a global alignment of two long words to comparisons of short windows, which is how bounds on longest common subsequences of encoded words are reduced to bounds for individual codewords.
--
--   **Formalization Note** The alignment maps are order embeddings `Fin N ↪o Fin x.length` and `Fin N ↪o Fin y.length`. The spanned interval is `indexSpan f S`, defined as `Finset.Icc (f (S.min' _)) (f (S.max' _))` for nonempty `S` (and empty otherwise), so its cardinality is $\ell_f$. `segment w b ℓ` is `(w.drop b).take ℓ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/SegmentComparison.lean#L97-L151

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

theorem OAI.TreeEdit.span_card_le_lcs {β : Type*} {N : ℕ} (x y : List β)
    (f : Fin N ↪o Fin x.length) (g : Fin N ↪o Fin y.length)
    (hfg : ∀ i, x.get (f i) = y.get (g i))
    (s : Finset (Fin N)) (hs : s.Nonempty) :
    s.card ≤ lcs (segment x (f (s.min' hs)).val (indexSpan f s).card)
      (segment y (g (s.min' hs)).val (indexSpan g s).card) := by sorry
