-- Prove2me | Theorems.Thm_OAI_C0Absorption_recomputed_global_bounds
-- name    : OAI.C0Absorption.recomputed_global_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:29:52.249714+00:00
-- url     : https://prove2.me/theorems/770c5d4f-a5ee-413e-ab43-cbc0b42def67
-- title:
--   Global bi-Lipschitz bounds for the recomputed shift
-- statement:
--   For frozen weights $W$ (block vectors $v$ with $|v|\le1$ and row functionals $w$ with $\sum|w|\le2$ and $\langle w,v\rangle=1$ on every block), the frozen shift $S_W$ is a linear map from $c_0$ to the block copy of $c_0$ with $\|S_Wx\|\le5\|x\|$ and $\|x\|\le5\|S_Wx\|$. The recomputed shift is $R(x)=S_{W(x/\|x\|)}\,x$, where $W(s)$ are the state weights read off from a point $s$ of the unit ball, and $\eta=1/1000$. For all $x,y\in c_0$,
--   $$
--   \Bigl(\tfrac15-24\eta\Bigr)\|x-y\|\le\|R(x)-R(y)\|\le(5+24\eta)\|x-y\| .
--   $$
--
--   Recomputing the weights at each point costs only $24\eta$ in the frozen constants.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Shift.lean#L290-L303

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.recomputed_global_bounds (x y : C0) :
    (1/5-24*eta)*dist x y≤dist (recomputedShift x) (recomputedShift y) ∧
    dist (recomputedShift x) (recomputedShift y)≤(5+24*eta)*dist x y := by sorry
