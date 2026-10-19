-- Prove2me | Theorems.Thm_OAI_C0Absorption_surjective_of_punctured_local_onto
-- name    : OAI.C0Absorption.surjective_of_punctured_local_onto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:27:46.668339+00:00
-- url     : https://prove2.me/theorems/3cf64044-7a25-46f4-a2da-07798f5add96
-- title:
--   Bi-Lipschitz maps that are locally onto away from zero are surjective
-- statement:
--   Let $E$ be a nontrivial real Banach space, $F$ a real normed space, and $f:E\to F$ Lipschitz and antilipschitz with $f(0)=0$. Suppose $F\setminus\{0\}$ is connected and the range of $f$ is a neighbourhood of $f(x)$ for every $x\ne0$. Then
--   $$
--   f(E)=F .
--   $$
--
--   Local surjectivity away from the origin propagates to global surjectivity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/LocalInverse.lean#L25-L57

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.C0Absorption.surjective_of_punctured_local_onto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial E]
    (f : E → F) {c C : ℝ≥0} (hf : AntilipschitzWith c f) (hLip : LipschitzWith C f)
    (hzero : f 0=0) (hconn : IsPreconnected ({0}ᶜ : Set F))
    (hlocal : ∀ x≠0, Set.range f∈nhds (f x)) : Function.Surjective f := by sorry
