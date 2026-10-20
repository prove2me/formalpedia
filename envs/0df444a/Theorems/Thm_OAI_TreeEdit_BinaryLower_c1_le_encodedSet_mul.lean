-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_c1_le_encodedSet_mul
-- name    : OAI.TreeEdit.BinaryLower.c1_le_encodedSet_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:11:19.185949+00:00
-- url     : https://prove2.me/theorems/1baef3db-73f2-45e9-bc0b-af0d85d60516
-- title:
--   Distortion transfers through a bi-Lipschitz block code
-- statement:
--   For a finite set $X$ with a distance $\rho$ (nonnegative, zero on the diagonal, positive off it) and $f:X\to\ell_1$, the distortion of $f$ is $\sup_{x\ne y}\frac{\|f(x)-f(y)\|}{\rho(x,y)}\cdot\sup_{x\ne y}\frac{\rho(x,y)}{\|f(x)-f(y)\|}$, and $c_1(X,\rho)$ is the infimum over injective $f$. Let $c$ encode letters of $\alpha$ by binary blocks of length $P$, and $W$ a set of at least two words of length $M$. Suppose for all words $x,y$ of length $M$,
--   $$
--   a\,\mathrm{ed}(x,y)\le\mathrm{ed}\bigl(c(x),c(y)\bigr)\le b\,\mathrm{ed}(x,y),\qquad a,b>0 .
--   $$
--   Then $c_1(W,\mathrm{ed})\le\frac ba\,c_1(c(W),\mathrm{ed})$.
--
--   Lower bounds for the source set give lower bounds for its binary encoding.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/EncodedImage.lean#L65-L99

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
universe u

theorem OAI.TreeEdit.BinaryLower.c1_le_encodedSet_mul {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (hupper : ∀ x y : Word α M,
      (ed (encode c x.val) (encode c y.val) : ℝ) ≤
        b * (ed x.val y.val : ℝ)) :
    c1 {x : Word α M // x ∈ W}
      (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        (b / a) * binarySetDistortion (encodedSet c W) := by sorry
