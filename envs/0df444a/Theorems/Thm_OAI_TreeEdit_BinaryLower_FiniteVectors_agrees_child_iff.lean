-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_agrees_child_iff
-- name    : OAI.TreeEdit.BinaryLower.FiniteVectors.agrees_child_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:01:58.020884+00:00
-- url     : https://prove2.me/theorems/d5eb7e10-8847-43dd-a90e-59d01a58edf3
-- title:
--   Agreement with a child leaf
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Fix positive integers $p(q,i)$ for levels $q<k$ and children $i<m$. Leaves are maps $a:\{0..k-1\}\to\{0..m-1\}$; $a,b$ agree to depth $j$ if $a_q=b_q$ for $q<j$. The prefix period is $\pi_j(a)=2\prod_{q<j}p(q,a_q)$, the leaf period $Q(a)=\pi_k(a)$, the level product $L_q=\prod_ip(q,i)$ and the suffix scale $s_j=\prod_{q\ge j}L_q$. For $j<k$, a leaf $a$, a child label $i$ and a leaf $b$, let $a[j\mapsto i]$ be $a$ with its level-$j$ entry replaced by $i$. Then
--   $$
--   a[j\mapsto i]\text{ agrees with }b\text{ to depth }j+1\iff a\text{ agrees with }b\text{ to depth }j\text{ and }b_j=i .
--   $$
--
--   This describes the subtree of the $i$-th child.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean#L110-L126

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteVectors
open scoped BigOperators
variable {m k : ℕ}

theorem OAI.TreeEdit.BinaryLower.FiniteVectors.agrees_child_iff (j : ℕ) (hj : j < k) (a b : Leaf m k) (i : Fin m) :
    Agrees (j + 1) (Function.update a ⟨j, hj⟩ i) b ↔
      Agrees j a b ∧ b ⟨j, hj⟩ = i := by sorry
