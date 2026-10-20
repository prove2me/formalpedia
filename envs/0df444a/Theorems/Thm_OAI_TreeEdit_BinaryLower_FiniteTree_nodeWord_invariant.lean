-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_invariant
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:58:29.583989+00:00
-- url     : https://prove2.me/theorems/2c12f47d-2014-4390-b64c-53ff815ca3e7
-- title:
--   Node words are invariant under shifts fixing the leaves below
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. For an additive group $A$, an alphabet $\Gamma$, leaf symbols $\lambda(p,x)$ and node shifts $u(p)\in A$, the node word is $\omega_0(p,x)=\lambda(p,x)$ and $\omega_{h+1}(p,x)=\Vert_{a<T}\Vert_{i<m}\,\omega_h(p\,i,\,x+a\,u(p))$. Let $z\in A$ and suppose every leaf below $p$ at height $h$ ignores the shift by $z$:
--   $$
--   \lambda(p\,q,\,x+z)=\lambda(p\,q,\,x)\qquad\text{for all }q\text{ with }|q|=h\text{ and all }x.
--   $$
--   Then $\omega_h(p,x+z)=\omega_h(p,x)$ for every $x$.
--
--   Only the leaf symbols see the state, so invariance at the leaves propagates upward.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeWords.lean#L56-L79

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
variable {A Γ : Type*} [AddCommMonoid A]

theorem OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_invariant {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (z : A)
    (hinv : ∀ q : List (Fin m), q.length = h → ∀ x : A,
      leaf (p ++ q) (x + z) = leaf (p ++ q) x) (x : A) :
    nodeWord T leaf u h p (x + z) = nodeWord T leaf u h p x := by sorry
