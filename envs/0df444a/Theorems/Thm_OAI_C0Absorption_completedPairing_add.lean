-- Prove2me | Theorems.Thm_OAI_C0Absorption_completedPairing_add
-- name    : OAI.C0Absorption.completedPairing_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:08:52.82702+00:00
-- url     : https://prove2.me/theorems/04d88e25-fa87-4f0c-b99a-f03e888cdf8a
-- title:
--   Additivity of extended test pairings
-- statement:
--   Let $Z$ be the completion of the molecules on a metric space $S$ under a selected norm, and let $f,g$ be bounded tests, i.e. $|\langle f,m\rangle|\le K\|m\|$ and similarly for $g$. Then for every $z\in Z$,
--   $$
--   \langle f+g,z\rangle=\langle f,z\rangle+\langle g,z\rangle .
--   $$
--
--   The extension of pairings from molecules to the completion is additive in the test function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Duality.lean#L77-L91

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem OAI.C0Absorption.completedPairing_add (f g : S → ℝ) (hf : BoundedTest L o f) (hg : BoundedTest L o g)
    (z : TestSpace L o) : completedPairing L o (fun s => f s+g s) z =
      completedPairing L o f z+completedPairing L o g z := by sorry
