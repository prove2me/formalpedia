-- Prove2me | Theorems.Thm_OAI_C0Absorption_absorption_upper
-- name    : OAI.C0Absorption.absorption_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:04:00.025458+00:00
-- url     : https://prove2.me/theorems/32aa00f8-86b9-4685-8ecd-8b9c31be66e1
-- title:
--   Upper Lipschitz bound for triangular absorption maps
-- statement:
--   Let $Q:Z\to U$ be a bounded linear map and $K:E\times U\to Z$ an $L_K$-Lipschitz map. The absorption map $F(x,e)=x+K(e,Qx)$ on $Z\times E$ satisfies
--   $$
--   d\bigl(F(x),F(y)\bigr)\le\bigl(1+L_K\max(1,\|Q\|)\bigr)\,d(x,y),
--   $$
--   where products carry the max metric.
--
--   Triangular perturbations of the identity are Lipschitz.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Triangular.lean#L35-L58

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

theorem OAI.C0Absorption.absorption_upper {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) {LK : ℝ}
    (hLK : 0 ≤ LK) (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y) :
    ∀ x y, dist (absorptionMap Q K x) (absorptionMap Q K y) ≤
      (1+LK * max 1 ‖Q‖) * dist x y := by sorry
