-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_characterSparse_detection
-- name    : OAI.TreeEdit.BinaryLower.FiniteActivity.characterSparse_detection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:49:55.519984+00:00
-- url     : https://prove2.me/theorems/4c9410e9-1380-44ac-bf46-828b3cda9721
-- title:
--   Sparse nodes are detected by multiples of the row vector
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $A$ be a finite abelian group, $w$ assign elements to tree nodes, and $v$ an internal node of depth $j$. Let $u=\sum_iw(v\,i)$ be the sum of its children's vectors, with $w(v)=R\,u$. Suppose $(Q\,p_i)\,w(v\,i)=0$ for each child, where $0<Q\le2k^{5j}$ and $0<p_i\le k^5$, $k\ge1$. If a character $\chi$ is sparse at $v$, i.e. $\chi(w(v))\ne1$ and fewer than $k$ children have $\chi(w(v\,i))\ne1$, then with $J=4k^{10k}$
--   $$
--   J\le\sum_{s=0}^{J-1}\bigl|1-\chi\bigl((s+1)\,u\bigr)\bigr|^2 .
--   $$
--
--   Sparse characters see the row translations by $u$ in at least half of the steps on average.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteVectorDetection.lean#L60-L90

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.BinaryLower.FiniteActivity.characterSparse_detection {α A : Type*}
    [Fintype α] [AddCommGroup A] [Finite A] {k : ℕ}
    (w : List α → A) (v : InternalNode α k) (u : A)
    (Q R : ℕ) (p : α → ℕ) (hk : 1 ≤ k)
    (hQpos : 0 < Q) (hQ : Q ≤ 2 * k ^ (5 * v.1.val))
    (hppos : ∀ i, 0 < p i) (hp : ∀ i, p i ≤ k ^ 5)
    (hroot : w (List.ofFn v.2) = R • u)
    (hsum : u = ∑ i, w (List.ofFn v.2 ++ [i]))
    (hchild : ∀ i, (Q * p i) • w (List.ofFn v.2 ++ [i]) = 0)
    (χ : AddChar A ℂ) (hsparse : characterSparse w k v χ) :
    ((4 * k ^ (10 * k) : ℕ) : ℝ) ≤
      ∑ s : Fin (4 * k ^ (10 * k)), ‖1 - χ ((s.val + 1) • u)‖ ^ 2 := by sorry
