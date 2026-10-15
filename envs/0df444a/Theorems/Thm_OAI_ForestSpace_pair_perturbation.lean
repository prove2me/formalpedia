-- Prove2me | Theorems.Thm_OAI_ForestSpace_pair_perturbation
-- name    : OAI.ForestSpace.pair_perturbation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:23:58.589615+00:00
-- url     : https://prove2.me/theorems/d74a73ad-f0b3-45b9-8895-85ef93e6dcd2
-- title:
--   Moving the base point in a lower bound for the symmetric average $\tfrac12(\|x+y\|+\|x-y\|)$
-- statement:
--   Let $E$ be a real normed space, let $x,a,y\in E$ with $\|x\|=1$, and let $b\ge0$ be a real number. If
--
--   $$
--   \sqrt{\|a\|^2+b}\ \le\ \frac{\|a+y\|+\|a-y\|}{2},
--   $$
--
--   then
--
--   $$
--   \sqrt{1+b}\ \le\ \frac{\|x+y\|+\|x-y\|}{2}+2\|x-a\| .
--   $$
--
--   So a lower bound of the form $\sqrt{\|a\|^2+b}$ for the symmetric average at a point $a$ transfers to any unit vector $x$, at an additive cost of twice the distance $\|x-a\|$. It is used to pass from the head approximation $a=P_Hx$ of a unit functional $x$, where the head–tail paired estimate applies, back to $x$ itself when bounding the averaged asymptotic midpoint modulus from below.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/ModulusProofs.lean#L107-L127

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.pair_perturbation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x a y : E) (b : ℝ) (hb : 0 ≤ b) (hx : ‖x‖ = 1)
    (hpair : Real.sqrt (‖a‖^2+b) ≤ (‖a+y‖+‖a-y‖)/2) :
    Real.sqrt (1+b) ≤ (‖x+y‖+‖x-y‖)/2+2*‖x-a‖ := by sorry
