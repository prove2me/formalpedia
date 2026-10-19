-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_offset_deficit_le
-- name    : OAI.FiniteCircle.WordMatching.offset_deficit_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:11:42.382577+00:00
-- url     : https://prove2.me/theorems/f46d4ea4-4627-4c38-b6a4-0cfcae94c148
-- title:
--   Deficit bound from following one fixed offset of each block through a matching of encodings
-- statement:
--   Let $\alpha$ be an alphabet and $w\ge1$; a block code $c:\alpha\to\{0,1\}^w$ assigns to every letter $a$ a binary codeword $c(a)=(c(a)_0,\dots,c(a)_{w-1})$, and the encoding of a word $x=x_0x_1\cdots x_{L-1}$ is the concatenation $\operatorname{enc}_c(x)=c(x_0)\,c(x_1)\cdots c(x_{L-1})\in\{0,1\}^{wL}$; positions are numbered from $0$, so position $iw+r$ with $0\le r<w$ of $\operatorname{enc}_c(x)$ is bit $r$ of the codeword of $x_i$ (the $i$-th block). For words $u,v$ let $\operatorname{lcs}(u,v)$ be the maximal length of a common subsequence and $\operatorname{def}(u,v)=|u|-\operatorname{lcs}(u,v)$ the deficit. Let $x,y$ be words over $\alpha$ and let $A$ be a matching of size $q$ between $\operatorname{enc}_c(x)$ and $\operatorname{enc}_c(y)$: strictly increasing maps $\lambda,\rho$ from $\{0,\dots,q-1\}$ to the positions of $\operatorname{enc}_c(x)$, respectively $\operatorname{enc}_c(y)$, with equal bits at $\lambda(k)$ and $\rho(k)$.
--
--   Fix an offset $p\in\mathbb{N}$. Block $i$ is *matched at $p$* if $\lambda(k)=iw+p$ for some $k$, and block $i$ is a *duplicate at $p$* if there are $k,l$ with $\lambda(k)=iw+p$, $\lambda(l)=(i+1)w+p$ and $\lfloor\rho(k)/w\rfloor=\lfloor\rho(l)/w\rfloor$, i.e. the offset-$p$ bits of the consecutive blocks $i$ and $i+1$ are matched into the same block of $\operatorname{enc}_c(y)$. Let $G\subseteq\{0,\dots,|x|-1\}$ and assume the labels are correct at offset $p$ on $G$: for every $i\in G$ and every $k$ with $\lambda(k)=iw+p$, the block $j=\lfloor\rho(k)/w\rfloor$ of its partner (which automatically satisfies $j<|y|$) carries the same letter, $x_i=y_j$. Then
--   $$
--   \operatorname{def}(x,y)\ \le\ 2\Bigl(|x|-\#\{i\in G:\ i\text{ matched at }p\}\Bigr)+\#\{\,i\in G:\ i+1<|x|,\ i\text{ a duplicate at }p\,\}.
--   $$
--
--   Following the bit at offset $p$ of every block of $\operatorname{enc}_c(x)$ to the block of its partner produces a monotone letter-preserving assignment of positions of $x$ to positions of $y$, whose only defects are unmatched blocks and consecutive blocks sent to the same block; the theorem records the resulting bound. Averaging it over many offsets $p$ is the core of the lower bound for deficits of encodings by offset-local codes.
--
--   **Formalization Note** The label hypothesis is stated with optional indexing, `x[i]? = y[(A.right k).val / w]?`; for $i<|x|$ it is equivalent to the letter equality above, because $\lfloor\rho(k)/w\rfloor<|y|$ always holds. "Matched at $p$" and "duplicate at $p$" are `A.matchedAt w i p` and `A.duplicateAt w i p`. The offset $p$ is not required to be smaller than $w$, and the subtractions are in $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/OffsetRecovery.lean#L242-L289

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery

open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem OAI.FiniteCircle.WordMatching.offset_deficit_le (A : WordMatching (encode c x) (encode c y) q)
    (hw : 0 < w) (p : ℕ) (G : Finset ℕ) (hG : G ⊆ Finset.range x.length)
    (hlabels : ∀ i ∈ G, ∀ k : Fin q, (A.left k).val=i*w+p →
      x[i]? = y[(A.right k).val/w]?) :
    deficit x y ≤ 2*(x.length-(G.filter (fun i => A.matchedAt w i p)).card) +
      ((G.filter (fun i => i+1 < x.length)).filter (fun i => A.duplicateAt w i p)).card := by sorry
