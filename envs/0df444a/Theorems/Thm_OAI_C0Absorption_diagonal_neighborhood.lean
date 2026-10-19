-- Prove2me | Theorems.Thm_OAI_C0Absorption_diagonal_neighborhood
-- name    : OAI.C0Absorption.diagonal_neighborhood
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:34:42.427885+00:00
-- url     : https://prove2.me/theorems/4bce6103-e471-4142-b612-f3ca3a9b4ebd
-- title:
--   Uniform smallness near the diagonal
-- statement:
--   Let $X,Y$ be topological spaces, $G$ a normed group, $q:X\to Y$ continuous at $x$, and $A:Y\times Y\to G$ with $A(u,v)\to g$ as $(u,v)\to(q(x),q(x))$. Then for every $\varepsilon>0$ there is a neighbourhood $s$ of $x$ such that
--   $$
--   \|A(q(y),q(z))-g\|<\varepsilon\qquad(y,z\in s).
--   $$
--
--   A two-variable limit at a diagonal point gives uniform control on a product neighbourhood.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/FiniteShift.lean#L135-L150

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
open scoped NNReal BigOperators

theorem OAI.C0Absorption.diagonal_neighborhood {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup G] (q : X → Y) {x : X} (hq : ContinuousAt q x)
    (A : Y × Y → G) (g : G) (hA : Tendsto A (nhds (q x,q x)) (nhds g))
    {ε : ℝ} (hε : 0<ε) :
    ∃ s : Set X, s∈nhds x ∧ ∀ y∈s, ∀ z∈s, ‖A (q y,q z)-g‖<ε := by sorry
