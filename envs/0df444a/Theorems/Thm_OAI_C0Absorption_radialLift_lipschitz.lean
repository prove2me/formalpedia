-- Prove2me | Theorems.Thm_OAI_C0Absorption_radialLift_lipschitz
-- name    : OAI.C0Absorption.radialLift_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:07:13.742187+00:00
-- url     : https://prove2.me/theorems/99110a9d-2f8f-49f0-bdb7-1a677927ff61
-- title:
--   Radial lifts of 1-Lipschitz maps on the ball are 3-Lipschitz
-- statement:
--   Let $\zeta$ be a $1$-Lipschitz map from the closed unit ball of a normed space $E$ to a normed space $Z$ with $\zeta(0)=0$. Then its radial lift
--   $$
--   x\longmapsto\|x\|\,\zeta\Bigl(\frac x{\|x\|}\Bigr)
--   $$
--   is $3$-Lipschitz on all of $E$.
--
--   Lipschitz maps on the unit ball extend positively homogeneously with a controlled constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Triangular.lean#L159-L186

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
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators
variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem OAI.C0Absorption.radialLift_lipschitz (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) : LipschitzWith 3 (radialLift ζ) := by sorry
