-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_word_sparse_detection
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.word_sparse_detection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:50:40.324956+00:00
-- url     : https://prove2.me/theorems/d5b6a9ac-9a8b-497b-8921-7a42059b78ab
-- title:
--   Sparse detection for the concrete tree words
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let the periods $p(q,i)$ satisfy $0<p(q,i)\le k^5$, $k\ge1$, and let $w(\cdot),u(\cdot)$ be the word vectors. If a character $\chi$ of the word state group is sparse at an internal node $v$ for the activity $\chi(w(\cdot))\ne1$ with threshold $k$, then
--   $$
--   4k^{10k}\le\sum_{s=0}^{4k^{10k}-1}\bigl|1-\chi\bigl((s+1)\,u(v)\bigr)\bigr|^2 .
--   $$
--
--   The concrete vectors satisfy the algebraic hypotheses of sparse detection.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteWordDetection.lean#L113-L140

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open scoped BigOperators
open Classical
variable {m k : ℕ}

theorem OAI.TreeEdit.BinaryLower.FiniteTree.word_sparse_detection (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (hk : 1 ≤ k) (hppos : ∀ q i, 0 < primes q i)
    (hp : ∀ q i, primes q i ≤ k ^ 5)
    (v : FiniteActivity.InternalNode (Fin m) k)
    (χ : AddChar (State (wordPeriods primes)) ℂ)
    (hsparse : FiniteActivity.characterSparse (wordW primes i₀) k v χ) :
    ((4 * k ^ (10 * k) : ℕ) : ℝ) ≤
      ∑ s : Fin (4 * k ^ (10 * k)),
        ‖1 - χ ((s.val + 1) • wordU primes i₀ (List.ofFn v.2))‖ ^ 2 := by sorry
