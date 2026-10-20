-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_ParameterImage_exists_word_image_lower
-- name    : OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:03:53.368162+00:00
-- url     : https://prove2.me/theorems/0a90fd03-9686-4bee-ab95-515444b417e8
-- title:
--   Distortion lower bounds for images of words
-- statement:
--   Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$. Let $G:A\to\Gamma^n$ map a finite parameter set to words of length $n$, with $\mathrm{ed}(G a,G b)>0$ for some $a,b$, and $D\in\mathbb R$. Suppose that whenever $F:A\to\ell_1$ and $C>0$ satisfy $\mathrm{ed}(Ga,Gb)/C\le\|F(a)-F(b)\|\le\mathrm{ed}(Ga,Gb)$ for all $a,b$, then $D\le C$. Then $W=G(A)$ is a finite set of words with $|W|\ge2$ and
--   $$
--   D\le c_1(W,\mathrm{ed}) .
--   $$
--
--   This is the parameter-image lower bound specialized to edit distance on words.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean#L59-L83

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.ParameterImage
variable {A X : Type*} [Fintype A]

theorem OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower {Γ : Type*} {n : ℕ}
    (G : A → Word Γ n)
    (hsep : ∃ a b, 0 < ed (G a).val (G b).val)
    (D : ℝ)
    (hobstruction : ∀ (F : A → RealL1) (C : ℝ), 0 < C →
      (∀ a b, (ed (G a).val (G b).val : ℝ) / C ≤ ‖F a - F b‖ ∧
        ‖F a - F b‖ ≤ (ed (G a).val (G b).val : ℝ)) → D ≤ C) :
    ∃ W : Finset (Word Γ n),
      (∀ w, w ∈ W ↔ ∃ a, G a = w) ∧ 2 ≤ W.card ∧
      D ≤ c1 {w : Word Γ n // w ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) := by sorry
