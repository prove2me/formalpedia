-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_state_congr
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_state_congr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:59:57.054304+00:00
-- url     : https://prove2.me/theorems/a2575593-45e4-4b3d-a9d0-ae6308228042
-- title:
--   Node words depend only on their subtree coordinates
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let $Q$ be leaf periods, $\lambda$ the tagged leaf decoder, $u$ any node shifts and $p$ a node with $|p|+h=k$. If two states $x,y\in\prod_l\mathbb Z/Q(l)$ agree on every leaf extending $p$,
--   $$
--   x_l=y_l\qquad\text{whenever }p\text{ is a prefix of }l ,
--   $$
--   then $\omega_h(p,x)=\omega_h(p,y)$.
--
--   A node word only reads the coordinates of the leaves in its own subtree.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeGeometry.lean#L38-L63

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree

theorem OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_state_congr {T m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x y : State Q) (hagree : ∀ l : Leaf m k, p <+: l.val → x l = y l) :
    nodeWord T (leafDecoder Q base) u h p x =
      nodeWord T (leafDecoder Q base) u h p y := by sorry
