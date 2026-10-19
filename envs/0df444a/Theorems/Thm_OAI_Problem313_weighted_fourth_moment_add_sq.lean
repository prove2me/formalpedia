-- Prove2me | Theorems.Thm_OAI_Problem313_weighted_fourth_moment_add_sq
-- name    : OAI.Problem313.weighted_fourth_moment_add_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:50:29.54281+00:00
-- url     : https://prove2.me/theorems/a6f4b8a3-ec88-4a02-bb38-8a082c8b9825
-- title:
--   A Minkowski step for fourth moments
-- statement:
--   Let $w\ge0$ be weights on a finite set, $A,B$ real functions, and $a,b\ge0$ with
--   $$
--   \sum w\,A^4\le a^2,\qquad\sum w\,B^4\le b^2 .
--   $$
--   Then $\sum w\,(A^2+B^2)^2\le(a+b)^2$.
--
--   This is the triangle inequality for the $L^2(w)$ norm applied to $A^2$ and $B^2$, written without square roots. It is the inductive step in tensorizing the two-point inequality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/HypercontractiveTensor.lean#L24-L52

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption

open OAI OAI.Problem313
universe u

theorem OAI.Problem313.weighted_fourth_moment_add_sq {α : Type u} (s : Finset α)
    (w A B : α → ℝ) (a b : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : (∑ x ∈ s, w x * (A x) ^ 4) ≤ a ^ 2)
    (hB : (∑ x ∈ s, w x * (B x) ^ 4) ≤ b ^ 2) :
    (∑ x ∈ s, w x * ((A x) ^ 2 + (B x) ^ 2) ^ 2) ≤ (a + b) ^ 2 := by sorry
