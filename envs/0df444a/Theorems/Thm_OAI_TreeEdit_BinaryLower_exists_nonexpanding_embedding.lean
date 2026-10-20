-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_exists_nonexpanding_embedding
-- name    : OAI.TreeEdit.BinaryLower.exists_nonexpanding_embedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:01:38.598767+00:00
-- url     : https://prove2.me/theorems/b29b19cf-bbd4-4bdd-b2d9-f6bef9445741
-- title:
--   Rescaling an embedding to be non-expanding
-- statement:
--   For a finite set $X$ with a distance $\rho$ (nonnegative, zero on the diagonal, positive off it) and $f:X\to\ell_1$, the distortion of $f$ is $\sup_{x\ne y}\frac{\|f(x)-f(y)\|}{\rho(x,y)}\cdot\sup_{x\ne y}\frac{\rho(x,y)}{\|f(x)-f(y)\|}$, and $c_1(X,\rho)$ is the infimum over injective $f$. Let $X$ have at least two points and $f:X\to\ell_1$ be injective with distortion $D$. Then $D>0$ and there is an injective $g:X\to\ell_1$ with
--   $$
--   \frac{\rho(x,y)}D\le\|g(x)-g(y)\|\le\rho(x,y)\qquad\text{for all }x,y .
--   $$
--
--   Equivalently one may normalize embeddings to be $1$-Lipschitz with contraction exactly controlled by the distortion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Distortion.lean#L331-L363

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

theorem OAI.TreeEdit.BinaryLower.exists_nonexpanding_embedding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) :
    0 < distortion ρ f ∧ ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y / distortion ρ f ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y := by sorry
