-- Prove2me | Theorems.Thm_OAI_FiniteCircle_deficit_le_sum_blocks
-- name    : OAI.FiniteCircle.deficit_le_sum_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:18:32.884318+00:00
-- url     : https://prove2.me/theorems/6e446b62-c41b-4c65-ba27-20055e5400b9
-- title:
--   The LCS deficit of two words cut into $b$ aligned blocks is at most the sum of the blockwise deficits
-- statement:
--   For finite words $x,y$ over an arbitrary alphabet let $\operatorname{lcs}(x,y)$ be the length of a longest common (not necessarily contiguous) subsequence, and define the *deficit* $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$. For a word $x$ and natural numbers $p,\ell$ write $x[p,p+\ell)$ for the segment of $x$ consisting of the letters in positions $p,p+1,\dots,p+\ell-1$, positions being counted from $0$.
--
--   **Theorem.** Let $b,m$ be natural numbers and let $x,y$ be words with $|x|=|y|=bm$. Then
--
--   $$
--   \operatorname{def}(x,y)\ \le\ \sum_{j=0}^{b-1}\operatorname{def}\bigl(x[jm,jm+m),\,y[jm,jm+m)\bigr).
--   $$
--
--   Cutting two words of equal length into $b$ aligned blocks of length $m$ can only increase the total deficit, because common subsequences of corresponding blocks concatenate to a common subsequence of the whole words. In the recursive construction of $\ell^1$ embeddings of edit distance, words of length $bm$ are embedded through their blocks of length $m$; this inequality is the step showing that the new embedding does not contract distances, since the deficit of the long words is dominated by the sum of the blockwise deficits, each of which is detected separately.
--
--   **Formalization Note** The segment is `segment x (j*m) m = (x.drop (j*m)).take m` and `deficit x y = x.length - lcs x y` with natural subtraction; no truncation occurs, since $\operatorname{lcs}(x,y)\le|x|$. The sum ranges over `j : Fin b`; for $b=0$ both words are empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Windows.lean#L155-L175

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.deficit_le_sum_blocks {α : Type*} {x y : List α} {b m : ℕ}
    (hx : x.length = b*m) (hy : y.length = b*m) :
    deficit x y ≤ ∑ j : Fin b, deficit (segment x (j*m) m) (segment y (j*m) m) := by sorry
