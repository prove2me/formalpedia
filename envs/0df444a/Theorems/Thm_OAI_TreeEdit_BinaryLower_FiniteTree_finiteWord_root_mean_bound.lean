-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_finiteWord_root_mean_bound
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_root_mean_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:57:34.830874+00:00
-- url     : https://prove2.me/theorems/046b0c8d-6dbf-4dbc-b341-c0d38e2ac704
-- title:
--   Lipschitz maps barely move the root translation on average
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let $k\ge1$, $0<p(q,i)\le k^5$, $J=4k^{10k}\le T$, and let $G$ be the root words. Suppose $F$ from the state group to $\ell_1$ is $1$-Lipschitz for edit distance: $\|F(x)-F(y)\|\le\mathrm{ed}(G(x),G(y))$. Then with $w=w(\varnothing)$,
--   $$
--   \mathbb E_x\|F(x+w)-F(x)\|\le4\Bigl(k\cdot\frac{2J}T(mT)^k+\frac{(mT)^k}{2k^k}\Bigr).
--   $$
--
--   Relative to the word length $(mT)^k$, the right side is small.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteWordL1Mean.lean#L39-L86

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
open Classical
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_root_mean_bound {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (i₀ : Fin m) (hk : 1 ≤ k)
    (hppos : ∀ q i, 0 < p q i) (hp : ∀ q i, p q i ≤ k ^ 5)
    (T : ℕ) (hT : 0 < T) (hJT : 4 * k ^ (10 * k) ≤ T)
    [Fintype (State (wordPeriods p))]
    (F : State (wordPeriods p) → RealL1)
    (hF : ∀ x y, ‖F x - F y‖ ≤
      (ed (finiteWord p i₀ T k [] x) (finiteWord p i₀ T k [] y) : ℝ)) :
    (𝔼 x : State (wordPeriods p), ‖F (x + wordW p i₀ []) - F x‖) ≤
      4 * ((k : ℝ) * ((2 * ((4 * k ^ (10 * k) : ℕ) : ℝ) / T) *
        ((m * T : ℕ) : ℝ) ^ k) +
        ((m * T : ℕ) : ℝ) ^ k / (2 * (k : ℝ) ^ k)) := by sorry
