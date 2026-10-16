-- Prove2me | Theorems.Thm_OAI_TreeEdit_Delimiter_alignment_bound
-- name    : OAI.TreeEdit.Delimiter.alignment_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:18:14.251854+00:00
-- url     : https://prove2.me/theorems/33f133bf-5a97-40f1-83be-764c77b24a96
-- title:
--   Common subsequences of synchronized block encodings descend to the source words
-- statement:
--   Let $\alpha$ be an alphabet, $B\ge 1$ an integer, and $c:\alpha\to\{0,1\}^B$ a binary block code. For a finite word $x=x_0x_1\cdots x_{n-1}$ over $\alpha$ let $E(x)=c(x_0)\,c(x_1)\cdots c(x_{n-1})\in\{0,1\}^{nB}$ be its concatenation encoding, and for a binary word $u$ let $u[n,n+B)$ be its factor of length $B$ starting at position $n$ (positions are numbered from $0$). The code $c$ is called *synchronizing* if for every finite word $x$ over $\alpha$, every letter $a\in\alpha$ and every $n$ with $n+B\le|E(x)|$,
--   $$
--   E(x)[n,n+B)=c(a)\ \Longrightarrow\ \text{there is } i<|x| \text{ with } n=iB \text{ and } x_i=a,
--   $$
--   that is, codewords occur in an encoding only at block boundaries, and there they identify the encoded letter.
--
--   **Theorem.** Let $c$ be synchronizing, let $M,N\ge 0$ be integers and let $x,y\in\alpha^M$ be words of length $M$. Suppose $f,g:\{0,\dots,N-1\}\to\{0,\dots,MB-1\}$ are strictly increasing maps with $E(x)_{f(i)}=E(y)_{g(i)}$ for all $i<N$, so that $f,g$ exhibit a common subsequence of length $N$ of the two encodings. Then
--   $$
--   M\le\operatorname{LCS}(x,y)+2\,(MB-N),
--   $$
--   where $\operatorname{LCS}(x,y)$ is the length of a longest (not necessarily contiguous) common subsequence of $x$ and $y$.
--
--   Applied to an optimal alignment of the encodings ($N=\operatorname{LCS}(E(x),E(y))$), the theorem gives $M-\operatorname{LCS}(x,y)\le 2\,\big(MB-\operatorname{LCS}(E(x),E(y))\big)$: the LCS deficit of two equal-length words is at most twice the LCS deficit of their encodings. This is how a synchronizing code transfers lower bounds on LCS deficit, and hence on edit distance, from a large alphabet to binary strings.
--
--   **Formalization Note** Words of length $M$ are the subtype `Word α M` of lists; $f,g$ are order embeddings `Fin N ↪o Fin (M*B)`; `Synchronizing c` is stated for lists of every length using `segment u n B = (u.drop n).take B`. The difference $MB-N$ is natural-number subtraction, but $N\le MB$ holds automatically because $f$ is injective.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Delimiter.lean#L75-L132

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
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter

open OAI OAI.TreeEdit OAI.TreeEdit.Delimiter
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.Delimiter.alignment_bound {α : Type*} {M B N : ℕ} (hB : 0 < B)
    (c : α → Word Bool B) (hc : Synchronizing c) (x y : Word α M)
    (f g : Fin N ↪o Fin (M*B))
    (hfg : ∀ i, (encode c x.val).get (Fin.cast (by rw [length_encode, x.property]) (f i)) =
      (encode c y.val).get (Fin.cast (by rw [length_encode, y.property]) (g i))) :
    M ≤ lcs x.val y.val + 2*(M*B-N) := by sorry
