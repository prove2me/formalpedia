-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_extendPrefix_append
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.extendPrefix_append
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:05:06.763161+00:00
-- url     : https://prove2.me/theorems/75bb89d3-1427-43f6-ad9f-668dec9e1290
-- title:
--   Extending a prefix by one child
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let $i_0$ be the default child and extend a node $p$ with $|p|<k$ to a full leaf $\bar p$ by filling the missing levels with $i_0$. Then for every child label $i$,
--   $$
--   \overline{p\,i}=\bar p\,[\,|p|\mapsto i\,],
--   $$
--   i.e. extending $p\,i$ agrees with extending $p$ and then setting level $|p|$ to $i$.
--
--   So child vectors are obtained from parent vectors by one coordinate update.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeInstantiation.lean#L43-L59

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree

theorem OAI.TreeEdit.BinaryLower.FiniteTree.extendPrefix_append {m k : ℕ} (i₀ i : Fin m) (p : List (Fin m))
    (hp : p.length < k) :
    extendPrefix i₀ (p ++ [i]) = Function.update (extendPrefix i₀ p) ⟨p.length, hp⟩ i := by sorry
