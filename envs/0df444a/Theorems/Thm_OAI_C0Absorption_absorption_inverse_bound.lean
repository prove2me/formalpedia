-- Prove2me | Theorems.Thm_OAI_C0Absorption_absorption_inverse_bound
-- name    : OAI.C0Absorption.absorption_inverse_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:05:57.477378+00:00
-- url     : https://prove2.me/theorems/cc442969-0d69-4fb7-82b6-9a9edf13962e
-- title:
--   Lower Lipschitz bound for triangular absorption maps
-- statement:
--   Let $F(x,e)=x+K(e,Qx)$ with $Q$ bounded linear and $K$ $L_K$-Lipschitz. Suppose there is $g:E\times U\to U$ with $c_g\,d(a,b)\le d(g(a),g(b))$ ($c_g>0$) and
--   $$
--   Q\bigl(K(e,u)\bigr)=g(e,u)-u .
--   $$
--   Then
--   $$
--   d(x,y)\le\max\Bigl(1+\frac{L_K\|Q\|}{c_g},\ \frac{\|Q\|}{c_g}\Bigr)\,d\bigl(F(x),F(y)\bigr).
--   $$
--
--   If the correction is invertible through $Q$, the absorption map is bi-Lipschitz.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Triangular.lean#L60-L95

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open Set Filter Topology
open scoped NNReal BigOperators
variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem OAI.C0Absorption.absorption_inverse_bound {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    {LK cg : ℝ} (hLK : 0 ≤ LK) (hcg : 0 < cg)
    (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y)
    (hg : ∀ x y, cg * dist x y ≤ dist (g x) (g y))
    (hQK : ∀ x : E × U, Q (K x) = g x-x.2) :
    ∀ x y, dist x y ≤ max (1+LK*‖Q‖/cg) (‖Q‖/cg) *
      dist (absorptionMap Q K x) (absorptionMap Q K y) := by sorry
