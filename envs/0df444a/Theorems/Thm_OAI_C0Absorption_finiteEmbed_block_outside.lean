-- Prove2me | Theorems.Thm_OAI_C0Absorption_finiteEmbed_block_outside
-- name    : OAI.C0Absorption.finiteEmbed_block_outside
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:32:13.390073+00:00
-- url     : https://prove2.me/theorems/23e84414-f08b-4f30-8fbe-b5e744cf6c08
-- title:
--   Finite embedding vanishes on blocks of higher level
-- statement:
--   For $N\in\mathbb N$ the finite model $\mathbb R^{\Lambda_N}$ has one row coordinate for each $i\le N$ and one coordinate for each block element of each level $(i,n)$ with $i,n\le N$, with the sup norm; the finite embedding places these coordinates at their row and label positions in $c_0$, an isometry. Let $x\in\mathbb R^{\Lambda_N}$ and let $\gamma$ be a label whose level $(i,n)$ satisfies $i>N$ or $n>N$. Then the embedded vector has
--   $$
--   (\iota_Nx)_{\mathrm{label}(\gamma)}=0 .
--   $$
--
--   The embedded finite model is supported on rows and blocks of level at most $N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Finite.lean#L119-L132

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

theorem OAI.C0Absorption.finiteEmbed_block_outside {N : ℕ} (x : FInput N) (γ : Label)
    (hγ : N < γ.level.1 ∨ N < γ.level.2) : finiteEmbed N x (labelIndex γ)=0 := by sorry
