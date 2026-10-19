-- Prove2me | Theorems.Thm_OAI_C0Absorption_finiteRecomputed_local_onto
-- name    : OAI.C0Absorption.finiteRecomputed_local_onto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:35:45.916921+00:00
-- url     : https://prove2.me/theorems/d8111538-9cc2-415b-946f-e4dfc380efe7
-- title:
--   The finite recomputed shift is locally onto away from the origin
-- statement:
--   For $N\in\mathbb N$ the finite model $\mathbb R^{\Lambda_N}$ has one row coordinate for each $i\le N$ and one coordinate for each block element of each level $(i,n)$ with $i,n\le N$, with the sup norm; the finite embedding $\iota_N$ places these coordinates at their row and label positions in $c_0$, an isometry. The finite recomputed shift is $R_N(x)=S^N_{W(\iota_Nx/\|x\|)}\,x$, the finite frozen shift with the state weights computed at the normalized embedded point. For every $x\ne0$ in $\mathbb R^{\Lambda_N}$,
--   $$
--   R_N(\mathbb R^{\Lambda_N})\ \text{is a neighbourhood of}\ R_N(x) .
--   $$
--
--   Near a nonzero point the map is a small Lipschitz perturbation of an invertible linear map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Continuity.lean#L95-L128

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

theorem OAI.C0Absorption.finiteRecomputed_local_onto {x : FInput N} (hx : x≠0) :
    Set.range (finiteRecomputed N)∈nhds (finiteRecomputed N x) := by sorry
