-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_descendant_normalized_bound
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_normalized_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:56:06.477462+00:00
-- url     : https://prove2.me/theorems/2f0c8e7b-8fda-4ccb-9e64-455db135f327
-- title:
--   Normalized cost of row-advancing shifts below a descendant
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. For an additive group $A$, leaf symbols $\lambda(p,x)$ and node shifts $u(p)\in A$, node words are $\omega_0(p,x)=\lambda(p,x)$ and $\omega_{h+1}(p,x)=\Vert_{a<T}\Vert_{i<m}\,\omega_h(p\,i,\,x+a\,u(p))$; write $\mathrm{ed}$ for edit distance. Let $m,T>0$, a node $p$, a path $q$, and $s\le T$. Suppose the shift by $s\,u(p\,q)$ fixes every leaf below $p$ outside the subtree of $p\,q$. Then for every $x$,
--   $$
--   \mathrm{ed}\bigl(\omega_{N}(p,x),\ \omega_N(p,x+s\,u(p\,q))\bigr)\le\frac{2s}T\cdot\frac{(mT)^N}{m^{|q|}},\qquad N=h+1+|q| .
--   $$
--
--   Advancing rows deep in the tree is cheap relative to the word length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeCosts.lean#L207-L233

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

theorem OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_normalized_bound {m : ℕ} (T : ℕ)
    (hm : 0 < m) (hT : 0 < T)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (s : ℕ) (hs : s ≤ T)
    (houtside : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leaf (p ++ r) (y + s • u (p ++ q)) = leaf (p ++ r) y)
    (x : A) :
    (ed (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q))) : ℝ) ≤
      (2 * (s : ℝ) / T) *
        (((m * T : ℕ) : ℝ) ^ (h + 1 + q.length) / (m : ℝ) ^ q.length) := by sorry
