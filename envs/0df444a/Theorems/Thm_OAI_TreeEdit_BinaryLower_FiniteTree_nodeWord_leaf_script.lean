-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_leaf_script
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_leaf_script
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:54:56.574999+00:00
-- url     : https://prove2.me/theorems/2d86cfb4-d5c3-4383-9d95-bd3105084117
-- title:
--   Edit cost of a shift affecting a single leaf
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. For an additive group $A$, leaf symbols $\lambda(p,x)$ and node shifts $u(p)\in A$, node words are $\omega_0(p,x)=\lambda(p,x)$ and $\omega_{h+1}(p,x)=\Vert_{a<T}\Vert_{i<m}\,\omega_h(p\,i,\,x+a\,u(p))$; write $\mathrm{ed}$ for edit distance. Let $p$ be a node, $q$ a path and $z\in A$ such that every leaf $p\,r$ with $|r|=|q|$ and $r\ne q$ ignores the shift by $z$. Then there is an edit script of length $T^{|q|}$ from $\omega_{|q|}(p,x)$ to $\omega_{|q|}(p,x+z)$, for every $x$:
--   $$
--   \mathrm{ed}\bigl(\omega_{|q|}(p,x),\ \omega_{|q|}(p,x+z)\bigr)\le T^{|q|} .
--   $$
--
--   Only the $T^{|q|}$ occurrences of the leaf $p\,q$ can change, by one substitution each.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeCosts.lean#L124-L147

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open CheapTranslations
variable {A Γ : Type*} [AddCommMonoid A]

theorem OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_leaf_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (q p : List (Fin m)) (z : A)
    (houtside : ∀ r : List (Fin m), r.length = q.length → r ≠ q →
      ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y)
    (x : A) :
    EditScript (nodeWord T leaf u q.length p x)
      (nodeWord T leaf u q.length p (x + z)) (T ^ q.length) := by sorry
