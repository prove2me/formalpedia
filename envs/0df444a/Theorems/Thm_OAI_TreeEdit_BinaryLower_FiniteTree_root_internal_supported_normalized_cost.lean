-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_root_internal_supported_normalized_cost
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.root_internal_supported_normalized_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:56:51.477486+00:00
-- url     : https://prove2.me/theorems/34500486-122d-4636-831e-1e04895a4024
-- title:
--   Root cost of a row shift supported on a subtree
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let $m,T>0$, leaf periods $Q$ with the tagged decoder, node shifts $u$, and an internal node $q$ of height $h+1$ (so $h+1+|q|=k$). Suppose $u(q)$ is supported on the leaves below $q$, and $s\le T$. Then for every state $x$,
--   $$
--   \mathrm{ed}\bigl(G(x),\,G(x+s\,u(q))\bigr)\le\frac{2s}T\cdot\frac{(mT)^k}{m^{|q|}},
--   $$
--   where $G=\omega_k(\varnothing,\cdot)$ is the root word.
--
--   Deep row shifts move the root word by a small fraction of its length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeConcreteCosts.lean#L91-L113

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

theorem OAI.TreeEdit.BinaryLower.FiniteTree.root_internal_supported_normalized_cost {m k : ℕ} (T : ℕ)
    (hm : 0 < m) (hT : 0 < T)
    (Q : Leaf m k → ℕ) (base : Leaf m k)
    (u : List (Fin m) → State Q) (h : ℕ) (q : List (Fin m))
    (hlen : h + 1 + q.length = k) (s : ℕ) (hs : s ≤ T)
    (hsupport : ∀ l : Leaf m k, ¬ q.IsPrefix l.val → u q l = 0)
    (x : State Q) :
    (ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + s • u q)) : ℝ) ≤
      (2 * (s : ℝ) / T) * (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ q.length) := by sorry
