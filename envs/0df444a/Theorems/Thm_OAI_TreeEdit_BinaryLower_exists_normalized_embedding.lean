-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_exists_normalized_embedding
-- name    : OAI.TreeEdit.BinaryLower.exists_normalized_embedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:00:48.134922+00:00
-- url     : https://prove2.me/theorems/87eac364-3087-4816-9cb7-de1fd03e01c6
-- title:
--   Rescaling an embedding to be non-contracting
-- statement:
--   For a finite set $X$ with a distance $\rho$ (nonnegative, zero on the diagonal, positive off it) and $f:X\to\ell_1$, the distortion of $f$ is $\sup_{x\ne y}\frac{\|f(x)-f(y)\|}{\rho(x,y)}\cdot\sup_{x\ne y}\frac{\rho(x,y)}{\|f(x)-f(y)\|}$, and $c_1(X,\rho)$ is the infimum over injective $f$. Let $X$ have at least two points and $f:X\to\ell_1$ be injective with distortion $D$. Then there is an injective $g:X\to\ell_1$ with
--   $$
--   \rho(x,y)\le\|g(x)-g(y)\|\le D\,\rho(x,y)\qquad\text{for all }x,y .
--   $$
--
--   A suitable multiple of $f$ never contracts and expands by at most $D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Distortion.lean#L276-L315

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped ENNReal
variable {X Y : Type*}

theorem OAI.TreeEdit.BinaryLower.exists_normalized_embedding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) :
    ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ distortion ρ f * ρ x y := by sorry
