-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_fixed_length_binary_conversion
-- name    : OAI.TreeEdit.BinaryLower.fixed_length_binary_conversion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:53:34.308384+00:00
-- url     : https://prove2.me/theorems/25c8d628-6af1-4e49-a99d-6d94d7a43c43
-- title:
--   A fixed-length binary block code preserving edit distance up to constants
-- statement:
--   There is $M_0$ such that for every $M\ge M_0$ and every finite alphabet $\Gamma$ with $1\le|\Gamma|\le M$ there is a code $c:\Gamma\to\{0,1\}^{M^2}$ with the following properties. For every word $x\in\Gamma^M$ the encoding $c(x)$, obtained by concatenating codewords, has length $M^3$, and for all $x,y\in\Gamma^M$
--   $$
--   \frac{M^2}{804}\,\mathrm{ed}(x,y)\le\mathrm{ed}\bigl(c(x),c(y)\bigr)\le M^2\,\mathrm{ed}(x,y),\qquad\frac{M^2}{402}\,D(x,y)\le D\bigl(c(x),c(y)\bigr).
--   $$
--
--   Here $\mathrm{ed}$ is the unit-cost edit distance and $D(u,v)=n-\mathrm{lcs}(u,v)$ is the deficit of two words of length $n$. A single binary code of polynomial width thus embeds equal-length words over an alphabet of size at most $M$ into binary words, scaling edit distance by $M^2$ up to an absolute constant factor.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FixedLengthBinaryConversion.lean#L15-L46

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
universe u

theorem OAI.TreeEdit.BinaryLower.fixed_length_binary_conversion :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ (Γ : Type u) [Fintype Γ],
        1 ≤ Fintype.card Γ → Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2),
          (∀ x : Word Γ M, (encode c x.val).length = M ^ 3) ∧
          ∀ x y : Word Γ M,
            (((M ^ 2 : ℕ) : ℝ) / 804 * (ed x.val y.val : ℝ) ≤
                (ed (encode c x.val) (encode c y.val) : ℝ)) ∧
            ((ed (encode c x.val) (encode c y.val) : ℝ) ≤
                ((M ^ 2 : ℕ) : ℝ) * (ed x.val y.val : ℝ)) ∧
            (((M ^ 2 : ℕ) : ℝ) / 402 * (deficit M x.val y.val : ℝ) ≤
                (deficit (M * M ^ 2) (encode c x.val) (encode c y.val) : ℝ)) := by sorry
