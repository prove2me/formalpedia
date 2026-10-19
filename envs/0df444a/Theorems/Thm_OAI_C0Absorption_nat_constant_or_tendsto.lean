-- Prove2me | Theorems.Thm_OAI_C0Absorption_nat_constant_or_tendsto
-- name    : OAI.C0Absorption.nat_constant_or_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:14:15.225981+00:00
-- url     : https://prove2.me/theorems/2d013fb5-f539-4f0b-b655-fdc4f2d7b903
-- title:
--   A natural sequence has a constant subsequence or tends to infinity
-- statement:
--   For every $f:\mathbb N\to\mathbb N$, either some value is attained along a subsequence,
--   $$
--   \exists a,\ \exists\varphi\ \text{strictly increasing}:\ f(\varphi(i))=a,
--   $$
--   or $f(i)\to\infty$.
--
--   This separates detecting tests with a fixed band from tests whose bands grow.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Selection.lean#L49-L64

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology

theorem OAI.C0Absorption.nat_constant_or_tendsto (f : ℕ → ℕ) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    Tendsto f atTop atTop := by sorry
