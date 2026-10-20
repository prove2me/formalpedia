-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_ParameterImage_image_lower_of_nonexpanding_obstruction
-- name    : OAI.TreeEdit.BinaryLower.ParameterImage.image_lower_of_nonexpanding_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:02:47.67684+00:00
-- url     : https://prove2.me/theorems/6b4a12b0-ee42-471f-9007-660d1f68015b
-- title:
--   Distortion lower bounds for images of parameter spaces
-- statement:
--   For a finite set $X$ with a distance $\rho$ (nonnegative, zero on the diagonal, positive off it) and $f:X\to\ell_1$, the distortion of $f$ is $\sup_{x\ne y}\frac{\|f(x)-f(y)\|}{\rho(x,y)}\cdot\sup_{x\ne y}\frac{\rho(x,y)}{\|f(x)-f(y)\|}$, and $c_1(X,\rho)$ is the infimum over injective $f$. Let $G:A\to X$ take at least two values, and $D\in\mathbb R$. Suppose that whenever $F:A\to\ell_1$ and $C>0$ satisfy
--   $$
--   \frac{\rho(G a,G b)}C\le\|F(a)-F(b)\|\le\rho(G a,G b)\quad\text{for all }a,b,
--   $$
--   we have $D\le C$. Then the image $G(A)$ has at least two points and $c_1(G(A),\rho)\ge D$.
--
--   Obstructions for maps defined on the parameter space give distortion lower bounds for its image.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean#L33-L57

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

theorem OAI.TreeEdit.BinaryLower.ParameterImage.image_lower_of_nonexpanding_obstruction
    (G : A → X) (hG : ∃ a b, G a ≠ G b)
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (D : ℝ)
    (hobstruction : ∀ (F : A → RealL1) (C : ℝ), 0 < C →
      (∀ a b, ρ (G a) (G b) / C ≤ ‖F a - F b‖ ∧
        ‖F a - F b‖ ≤ ρ (G a) (G b)) → D ≤ C) :
    2 ≤ (image G).card ∧
      D ≤ c1 {x : X // x ∈ image G} (fun x y => ρ x.val y.val) := by sorry
