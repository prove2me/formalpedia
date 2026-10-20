-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_BlockRestriction_card_le_lcs_slices
-- name    : OAI.TreeEdit.BinaryLower.BlockRestriction.card_le_lcs_slices
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:15:56.983222+00:00
-- url     : https://prove2.me/theorems/71db51ac-fed1-49ab-af81-c3346008896f
-- title:
--   Matches inside two windows give a common subsequence of the windows
-- statement:
--   Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$. Let $u,v$ be strictly increasing position sequences in words $x,y$ with $x_{u_t}=y_{v_t}$ for all $t$. Let $s$ be a set of indices whose $u$-positions lie in the window $[a,a+A)$ and $v$-positions lie in $[b,b+B)$. Then
--   $$
--   |s|\le\mathrm{lcs}\bigl(x[a,a+A),\ y[b,b+B)\bigr),
--   $$
--   where $x[a,a+A)$ is the slice of $x$ obtained by dropping $a$ letters and keeping $A$.
--
--   So local match counts are controlled by longest common subsequences of slices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/BlockRestriction.lean#L15-L59

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
universe u
variable {α : Type u}

theorem OAI.TreeEdit.BinaryLower.BlockRestriction.card_le_lcs_slices (x y : List α) {n : ℕ}
    (u v : Fin n → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hxu : ∀ t, u t < x.length) (hyv : ∀ t, v t < y.length)
    (heq : ∀ t, x[u t]'(hxu t) = y[v t]'(hyv t))
    (s : Finset (Fin n)) (a b A B : ℕ)
    (hsu : ∀ t ∈ s, a ≤ u t ∧ u t < a + A)
    (hsv : ∀ t ∈ s, b ≤ v t ∧ v t < b + B) :
    s.card ≤ lcs ((x.drop a).take A) ((y.drop b).take B) := by sorry
