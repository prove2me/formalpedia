-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_singleton_deficit_of_ne
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.singleton_deficit_of_ne
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:00:38.412983+00:00
-- url     : https://prove2.me/theorems/9803e385-f483-407d-bf94-a51d7146e6b1
-- title:
--   Distinct single letters have deficit one
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$. If $a\ne b$ are letters, then the one-letter words $[a]$ and $[b]$ satisfy
--   $$
--   r_1([a],[b])=1-\mathrm{lcs}([a],[b])=1 .
--   $$
--
--   Different leaf symbols contribute a full unit of deficit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeGeometry.lean#L100-L118

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree

theorem OAI.TreeEdit.BinaryLower.FiniteTree.singleton_deficit_of_ne {Γ : Type*} (a b : Γ) (hab : a ≠ b) :
    deficit 1 [a] [b] = 1 := by sorry
