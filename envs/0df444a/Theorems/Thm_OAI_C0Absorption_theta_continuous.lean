-- Prove2me | Theorems.Thm_OAI_C0Absorption_theta_continuous
-- name    : OAI.C0Absorption.theta_continuous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:25:20.296081+00:00
-- url     : https://prove2.me/theorems/1428e849-d8f9-4a98-b7f6-e32f2e6a5d3d
-- title:
--   Continuity of the radial angle weights
-- statement:
--   For a terminal index $J$ and $j\in\mathbb N$, the angle weight $\theta_J(r)_j$ is defined by $\theta_J(r)_j=\sin\alpha_j(\log r)\cos\alpha_{j+1}(\log r)$ for $r>0$, built from piecewise transition angles $\alpha_j$. For $r\le0$ it is the indicator of $j=J$. The weights satisfy $\sum_{j\le J}\theta_J(r)_j^2=1$. For every $J$ and $j$, the function
--   $$
--   r\longmapsto\theta_J(r)_j
--   $$
--   is continuous on $\mathbb R$.
--
--   The two definitions glue because for small radii the angles already sit at their terminal values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Angles.lean#L254-L265

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
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.theta_continuous (J j : ℕ) : Continuous (fun r => theta J r j) := by sorry
