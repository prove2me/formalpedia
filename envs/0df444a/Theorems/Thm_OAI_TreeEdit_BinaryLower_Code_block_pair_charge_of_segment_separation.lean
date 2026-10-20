-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_block_pair_charge_of_segment_separation
-- name    : OAI.TreeEdit.BinaryLower.Code.block_pair_charge_of_segment_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:50:40.875151+00:00
-- url     : https://prove2.me/theorems/fcd8ab59-874c-4a09-9f83-dffb19804ae3
-- title:
--   Local charge for a long bad block pair
-- statement:
--   Let $x,y$ be words of length $MP$ over any alphabet, viewed as $M$ blocks of width $P>0$, and let $f,g:\{0,\dots,r-1\}\to\{0,\dots,MP-1\}$ be strictly increasing with $x_{f(t)}=y_{g(t)}$ for all $t$. Label each index by its block pair $\lambda(t)=(\lfloor f(t)/P\rfloor,\lfloor g(t)/P\rfloor)$, with fibres $F(b)$ and spans $\mathrm{Span}_f(b)$, $\mathrm{Span}_g(b)$. Assume block-segment separation at cutoff $a_0$: for each bad pair $(b_1,b_2)$ with $b_1,b_2<M$, all $a\ge a_0$, and all length-$a$ windows inside block $b_1$ of $x$ and block $b_2$ of $y$, every common subsequence $w$ of the two windows has $100|w|\le99a$. If $b$ is a bad pair with $F(b)$ nonempty and $|F(b)|\ge a_0$, then
--   $$
--   |F(b)|\le100\Bigl(\bigl(|\mathrm{Span}_f(b)|-|F(b)|\bigr)+\bigl(|\mathrm{Span}_g(b)|-|F(b)|\bigr)\Bigr).
--   $$
--
--   Every hundred matches inside a long bad block pair force at least one unmatched position in its two spans.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/UnequalSegments.lean#L36-L134

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code

theorem OAI.TreeEdit.BinaryLower.Code.block_pair_charge_of_segment_separation
    {α : Type*} {r M P : ℕ} (hP : 0 < P)
    (x y : Fin (M * P) → α)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (hmatch : ∀ t, x (f t) = y (g t))
    (bad : ℕ × ℕ → Prop) (a₀ : ℕ)
    (hsep : BlockSegmentSeparation x y bad a₀)
    (b : ℕ × ℕ) (hb : bad b)
    (hvisit : ∃ t, ((f t).val / P, (g t).val / P) = b)
    (hlarge : a₀ ≤
      (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) :
    (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card ≤
      100 * (((matchingSpan f (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) +
        ((matchingSpan g (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card)) := by sorry
