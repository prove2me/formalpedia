-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_symbol_prefix_of_mem
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.symbol_prefix_of_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:09:13.197983+00:00
-- url     : https://prove2.me/theorems/d7e588e9-50c7-482f-968f-b05373206316
-- title:
--   Symbols of a node word carry tags below the node
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let $Q$ be leaf periods, $\lambda$ the tagged leaf decoder and $p$ a node with $|p|+h=k$. If a tagged symbol $(l,r)$ occurs in the node word $\omega_h(p,x)$, then
--   $$
--   p\text{ is a prefix of }l .
--   $$
--
--   So the node word at $p$ uses only the subtree alphabet of $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeTags.lean#L15-L34

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree

theorem OAI.TreeEdit.BinaryLower.FiniteTree.symbol_prefix_of_mem {m k T : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State Q) (s : Symbol Q)
    (hs : s ∈ nodeWord T (leafDecoder Q base) u h p x) : p <+: s.1.val := by sorry
