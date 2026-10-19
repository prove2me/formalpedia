-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_suppress_involutive
-- name    : OAI.KervaireRibbon.suppress_involutive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:27:38.784852+00:00
-- url     : https://prove2.me/theorems/8c5d3cb8-eeaf-4330-bb64-0e96ec3ff0fa
-- title:
--   Suppression keeps the edge permutation an involution
-- statement:
--   Let $\theta$ be an involution of $D$ and $x\ne y$ darts with $\theta x\ne x$, $\theta x\ne y$ and $\theta y\ne y$. Let the suppressed edge permutation be
--   $$
--   \mathrm{supp}(\theta,x,y)=(x\ y)\,\bigl((y\ \theta x)\,\theta\,(y\ \theta x)\bigr).
--   $$
--   Then $\mathrm{supp}(\theta,x,y)$ is again an involution.
--
--   The darts $x$ and $y$ become fixed, and $\theta x$ is paired with $\theta y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Suppression.lean#L193-L210

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] in
theorem OAI.KervaireRibbon.suppress_involutive (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by sorry
