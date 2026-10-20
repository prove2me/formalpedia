-- Prove2me | Theorems.Thm_OAI_SingleFold_GrowthEstimate_bracket_unique
-- name    : OAI.SingleFold.GrowthEstimate.bracket_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:07:22.452+00:00
-- url     : https://prove2.me/theorems/4618e6e9-2e19-427b-a317-992c61420597
-- title:
--   Every integer has a unique bracket in a strictly increasing sequence
-- statement:
--   Let $W:\mathbb{N}\to\mathbb{N}$ be strictly increasing and unbounded. Then for every $u\in\mathbb{N}$ there is exactly one $k\ge1$ with
--   $$
--   W(k)\le u+W(1)<W(k+1) .
--   $$
--
--   The bracket index $k$ is the integer the compiler extracts from $u$; it grows like $\sqrt{\log u}$ when $\log W(j)\approx aj^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean#L41-L64

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion

open OAI OAI.SingleFold
open Filter
open scoped Topology
variable {W : ℕ → ℕ} {a c : ℝ}

theorem OAI.SingleFold.GrowthEstimate.bracket_unique (hW : StrictMono W) (hunb : ∀ U, ∃ j, U<W j) (u : ℕ) :
    ∃! k : ℕ, 1≤k ∧ W k≤u+W 1 ∧ u+W 1<W (k+1) := by sorry
