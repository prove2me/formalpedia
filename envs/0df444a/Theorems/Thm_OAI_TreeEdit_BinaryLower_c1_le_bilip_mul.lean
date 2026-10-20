-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_c1_le_bilip_mul
-- name    : OAI.TreeEdit.BinaryLower.c1_le_bilip_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:59:58.208037+00:00
-- url     : https://prove2.me/theorems/ec4c2adf-975d-4c6d-bae6-a8b07e0d6f36
-- title:
--   l1 distortion under bi-Lipschitz embeddings
-- statement:
--   For a finite set $X$ with distance $\rho$ and an injective $f:X\to\ell_1$, the distortion is $\sup_{x\ne y}\frac{\|f(x)-f(y)\|}{\rho(x,y)}\cdot\sup_{x\ne y}\frac{\rho(x,y)}{\|f(x)-f(y)\|}$, and $c_1(X,\rho)$ is its infimum over injective $f$. Let $(X,\rho)$, $(Y,\sigma)$ be finite with at least two points, $\rho>0$ off the diagonal, and $g:X\to Y$ injective with $a\rho\le\sigma\circ(g\times g)\le b\rho$, $a,b>0$. Then
--   $$
--   c_1(X,\rho)\le\frac ba\,c_1(Y,\sigma).
--   $$
--
--   A bi-Lipschitz copy of $X$ inside $Y$ transfers lower bounds for $c_1(X)$ to $c_1(Y)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Distortion.lean#L253-L274

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

theorem OAI.TreeEdit.BinaryLower.c1_le_bilip_mul [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (hσ : ∀ x y, 0 ≤ σ x y)
    (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (g : X → Y) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x y, a * ρ x y ≤ σ (g x) (g y))
    (hupper : ∀ x y, σ (g x) (g y) ≤ b * ρ x y) :
    c1 X ρ ≤ (b / a) * c1 Y σ := by sorry
