-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_ParameterImage_exists_word_image_lower_of_root_bound
-- name    : OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower_of_root_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:05:29.968009+00:00
-- url     : https://prove2.me/theorems/664a21e1-db0d-42b1-b9a2-262a83fb5341
-- title:
--   Distortion from a far translation that Lipschitz maps barely move
-- statement:
--   Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$. Let $A$ be a finite abelian group, $G:A\to\Gamma^n$, $z\in A$, and $\ell,\upsilon>0$. Suppose $\mathrm{ed}(G(x),G(x+z))\ge\ell$ for all $x$, and every $1$-Lipschitz $F:A\to\ell_1$ (for $\mathrm{ed}\circ G$) satisfies
--   $$
--   \frac1{|A|}\sum_x\|F(x+z)-F(x)\|\le\upsilon .
--   $$
--   Then the image $W=G(A)$ has $|W|\ge2$ and $c_1(W,\mathrm{ed})\ge\ell/\upsilon$.
--
--   A translation that is far in edit distance but short on average in every $\ell_1$ embedding forces distortion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean#L97-L135

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

theorem OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower_of_root_bound {Γ : Type*} {n : ℕ}
    [AddCommGroup A] (G : A → Word Γ n) (z : A)
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : 0 < upper)
    (hsep : ∀ x, lower ≤ (ed (G x).val (G (x + z)).val : ℝ))
    (hroot : ∀ F : A → RealL1,
      (∀ x y, ‖F x - F y‖ ≤ (ed (G x).val (G y).val : ℝ)) →
      (∑ x : A, ‖F (x + z) - F x‖) / Fintype.card A ≤ upper) :
    ∃ W : Finset (Word Γ n),
      (∀ w, w ∈ W ↔ ∃ a, G a = w) ∧ 2 ≤ W.card ∧
      lower / upper ≤ c1 {w : Word Γ n // w ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) := by sorry
