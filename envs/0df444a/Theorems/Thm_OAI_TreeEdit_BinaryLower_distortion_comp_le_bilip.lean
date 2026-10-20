-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_distortion_comp_le_bilip
-- name    : OAI.TreeEdit.BinaryLower.distortion_comp_le_bilip
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:59:06.51986+00:00
-- url     : https://prove2.me/theorems/1cea3e11-2b13-441e-b463-0a924fa58b4f
-- title:
--   Distortion under a bi-Lipschitz reparametrization
-- statement:
--   For a finite set $X$ with distance $\rho$ and an injective $f:X\to\ell_1$, the distortion is $\sup_{x\ne y}\frac{\|f(x)-f(y)\|}{\rho(x,y)}\cdot\sup_{x\ne y}\frac{\rho(x,y)}{\|f(x)-f(y)\|}$, and $c_1(X,\rho)$ is its infimum over injective $f$. Let $(X,\rho)$ and $(Y,\sigma)$ be finite with at least two points, $\rho>0$ off the diagonal, and $g:X\to Y$ injective with
--   $$
--   a\,\rho(x,y)\le\sigma(g(x),g(y))\le b\,\rho(x,y),\qquad a>0 .
--   $$
--   Then for every $f:Y\to\ell_1$, the distortion of $f\circ g$ with respect to $\rho$ is at most $\frac ba$ times the distortion of $f$ with respect to $\sigma$.
--
--   Composition with a bi-Lipschitz map changes distortion by at most its own distortion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Distortion.lean#L197-L251

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

theorem OAI.TreeEdit.BinaryLower.distortion_comp_le_bilip [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (hσ : ∀ x y, 0 ≤ σ x y)
    (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (g : X → Y) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlower : ∀ x y, a * ρ x y ≤ σ (g x) (g y))
    (hupper : ∀ x y, σ (g x) (g y) ≤ b * ρ x y) (f : Y → RealL1) :
    distortion ρ (f ∘ g) ≤ (b / a) * distortion σ f := by sorry
