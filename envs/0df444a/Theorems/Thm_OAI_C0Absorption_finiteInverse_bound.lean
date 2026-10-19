-- Prove2me | Theorems.Thm_OAI_C0Absorption_finiteInverse_bound
-- name    : OAI.C0Absorption.finiteInverse_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:33:09.444252+00:00
-- url     : https://prove2.me/theorems/9bd09225-bc83-4642-82c4-203fa316b454
-- title:
--   Norm bound for the finite inverse of the frozen shift
-- statement:
--   For $N\in\mathbb N$ the finite model $\mathbb R^{\Lambda_N}$ has one row coordinate for each $i\le N$ and one coordinate for each block element of each level $(i,n)$ with $i,n\le N$, with the sup norm; the finite embedding places these coordinates at their row and label positions in $c_0$, an isometry. For frozen weights $W$ (block vectors $v$ with $|v|\le1$ and rows $w$ with $\sum|w|\le2$), the finite inverse $G_W$ sets each row coordinate $i$ to the row functional at level $(i,0)$. It sets each block coordinate $b$ of level $\ell$ to $y_b-v_b(w_\ell\cdot y-\mathrm{next}_\ell(y))$, where $\mathrm{next}_\ell$ is the row functional at the next level or the row input. Then
--   $$
--   \|G_W\,y\|_\infty\le5\|y\|_\infty .
--   $$
--
--   The explicit inverse has the same constant $5$ as the infinite frozen shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Finite.lean#L232-L245

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
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty
variable {N : ℕ}

theorem OAI.C0Absorption.finiteInverse_bound (W : FrozenWeights) (y : FInput N) : ‖finiteInverseFunction W y‖≤5*‖y‖ := by sorry
