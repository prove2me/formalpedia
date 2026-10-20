-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_exists_finite_source_family
-- name    : OAI.TreeEdit.BinaryLower.exists_finite_source_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:18:37.696625+00:00
-- url     : https://prove2.me/theorems/0d2b45f5-033a-4c0e-b92c-d172f7968e4a
-- title:
--   Finite-tree words with large l1 distortion over a moderate alphabet
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Write $\mathrm{growth}(c,d)=\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$, $M(k)=(20k\,k^{20k})^k$ for the source length, and $c_1(W)$ for the least distortion of an injective map of $(W,\mathrm{ed})$ into $\ell_1$. There are $c_0>0$ (namely $\frac1{34}$) and $K$ such that for every $k\ge K$ there is a finite alphabet $\Gamma$ with $1\le|\Gamma|\le M(k)$ and a set $W$ of at least two words of length $M(k)$ over $\Gamma$ with
--   $$
--   c_0\Bigl(\frac k4\Bigr)^k\le c_1(W,\mathrm{ed}) .
--   $$
--
--   The distortion grows like $k^k$ while the length is only $\exp(O(k^2\log k))$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteSourceFamily.lean#L17-L84

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open FiniteTree
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.exists_finite_source_family :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ Γ : Type, ∃ inst : Fintype Γ,
        1 ≤ @Fintype.card Γ inst ∧ @Fintype.card Γ inst ≤ finiteSourceLength k ∧
        ∃ W : Finset (Word Γ (finiteSourceLength k)), 2 ≤ W.card ∧
          c₀ * ((k : ℝ) / 4) ^ k ≤
            c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
              (fun x y => (ed x.val.val y.val.val : ℝ)) := by sorry
