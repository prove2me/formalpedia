-- Prove2me | Theorems.Thm_OAI_C0Absorption_finiteRecomputed_global_bounds
-- name    : OAI.C0Absorption.finiteRecomputed_global_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:33:57.201978+00:00
-- url     : https://prove2.me/theorems/11369658-b45b-4150-8ce6-39de3a46ff80
-- title:
--   Global bi-Lipschitz bounds for the finite recomputed shift
-- statement:
--   For $N\in\mathbb N$ the finite model $\mathbb R^{\Lambda_N}$ has one row coordinate for each $i\le N$ and one coordinate for each block element of each level $(i,n)$ with $i,n\le N$, with the sup norm; the finite embedding places these coordinates at their row and label positions in $c_0$, an isometry. The finite recomputed shift is $R_N(x)=S^N_{W(\iota_Nx/\|x\|)}\,x$, the finite frozen shift with the state weights computed at the normalized embedded point, and $\eta=1/1000$. For all $x,y$,
--   $$
--   \Bigl(\tfrac15-24\eta\Bigr)\|x-y\|\le\|R_N(x)-R_N(y)\|\le(5+24\eta)\|x-y\| .
--   $$
--
--   The finite truncations satisfy the same bounds as the infinite recomputed shift, uniformly in $N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/FiniteShift.lean#L64-L77

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
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty
variable {N : ℕ}

theorem OAI.C0Absorption.finiteRecomputed_global_bounds (x y : FInput N) :
    (1/5-24*eta)*dist x y≤dist (finiteRecomputed N x) (finiteRecomputed N y) ∧
    dist (finiteRecomputed N x) (finiteRecomputed N y)≤(5+24*eta)*dist x y := by sorry
