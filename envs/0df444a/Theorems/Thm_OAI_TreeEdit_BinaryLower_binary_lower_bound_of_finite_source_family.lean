-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_binary_lower_bound_of_finite_source_family
-- name    : OAI.TreeEdit.BinaryLower.binary_lower_bound_of_finite_source_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:12:24.579617+00:00
-- url     : https://prove2.me/theorems/1cafec1b-03c7-4077-8d30-998ec003c3e5
-- title:
--   Binary lower bound from a source family and a block code
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Write $\mathrm{growth}(c,d)=\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$, $M(k)=(20k\,k^{20k})^k$ for the source length, and $c_1(W)$ for the least distortion of an injective map of $(W,\mathrm{ed})$ into $\ell_1$. Assume two inputs. First, a binary code: for all $M\ge M_0$ and alphabets $\Gamma$ with $1\le|\Gamma|\le M$ there is $c:\Gamma\to\{0,1\}^{M^2}$ with $\frac{M^2}{804}\mathrm{ed}(x,y)\le\mathrm{ed}(c(x),c(y))$ for words of length $M$. Second, a source family: for $k\ge K$ there are an alphabet with $1\le|\Gamma|\le M(k)$ and a set $W$ of at least two words of length $M(k)$ with $c_1(W)\ge c_0(k/4)^k$. Then there are $c>0$ and $d_0$ such that every $d\ge d_0$ has $1\le n\le d$ and a set $V$ of at least two binary words of length $n$ with
--   $$
--   \mathrm{growth}(c,d)\le c_1(V).
--   $$
--
--   The large-alphabet obstruction carried by the source family thus transfers to equal-length binary words, at the cost of the explicit factor coming from the encoding.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteFamilyTransfer.lean#L29-L75

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
universe u

theorem OAI.TreeEdit.BinaryLower.binary_lower_bound_of_finite_source_family
    (hcode : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ (Γ : Type u) [Fintype Γ],
        1 ≤ Fintype.card Γ → Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2), ∀ x y : Word Γ M,
          (((M ^ 2 : ℕ) : ℝ) / 804) * (ed x.val y.val : ℝ) ≤
            (ed (encode c x.val) (encode c y.val) : ℝ))
    (hfamily : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ Γ : Type u, ∃ inst : Fintype Γ,
        1 ≤ @Fintype.card Γ inst ∧ @Fintype.card Γ inst ≤ finiteSourceLength k ∧
        ∃ W : Finset (Word Γ (finiteSourceLength k)), 2 ≤ W.card ∧
          c₀ * ((k : ℝ) / 4) ^ k ≤
            c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
              (fun x y => (ed x.val.val y.val.val : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by sorry
