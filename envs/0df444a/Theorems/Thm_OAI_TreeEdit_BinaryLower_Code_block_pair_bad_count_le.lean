-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_block_pair_bad_count_le
-- name    : OAI.TreeEdit.BinaryLower.Code.block_pair_bad_count_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:47:00.978573+00:00
-- url     : https://prove2.me/theorems/2aa699c3-402a-4406-9029-0383f10f0305
-- title:
--   Matches in bad block pairs are bounded by the deficit
-- statement:
--   Let $P>0$ and let $f,g:\{0,\dots,r-1\}\to\{0,\dots,MP-1\}$ be strictly increasing, viewed as an increasing matching between two words made of $M$ blocks of width $P$. Label each index by its block pair $\lambda(t)=(\lfloor f(t)/P\rfloor,\lfloor g(t)/P\rfloor)$; write $F(b)$ for the fibre of a pair $b$ and $\mathrm{Span}_f(b)$, $\mathrm{Span}_g(b)$ for the interval hulls of its positions on the two sides. Fix a set of bad block pairs and a cutoff $a_0$, and suppose every visited bad pair $b$ with $|F(b)|\ge a_0$ satisfies
--   $$
--   |F(b)|\le100\Bigl(\bigl(|\mathrm{Span}_f(b)|-|F(b)|\bigr)+\bigl(|\mathrm{Span}_g(b)|-|F(b)|\bigr)\Bigr).
--   $$
--
--   Then the number of indices $t$ whose block pair $\lambda(t)$ is bad is at most $200(MP-r)+2Ma_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/UnequalCounting.lean#L23-L67

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code

theorem OAI.TreeEdit.BinaryLower.Code.block_pair_bad_count_le {r M P : ℕ} (hP : 0 < P)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (bad : ℕ × ℕ → Prop) [DecidablePred bad] (a₀ : ℕ)
    (hlarge : ∀ b ∈ (Finset.univ.image (fun i => ((f i).val / P, (g i).val / P))).filter bad,
      a₀ ≤ (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card →
      (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card ≤
        100 * (((matchingSpan f (fun i => ((f i).val / P, (g i).val / P)) b).card -
          (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card) +
          ((matchingSpan g (fun i => ((f i).val / P, (g i).val / P)) b).card -
          (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card))) :
    (Finset.univ.filter (fun i => bad ((f i).val / P, (g i).val / P))).card ≤
      200 * (M * P - r) + 2 * M * a₀ := by sorry
