-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Box_separated_subset
-- name    : OAI.CriticalZ3.Box.separated_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:14:43.121764+00:00
-- url     : https://prove2.me/theorems/a3564b89-893e-4c2b-a729-1d9c760b2f0b
-- title:
--   Large vertex sets contain many well-separated points
-- statement:
--   Let $s\subseteq\mathbb Z^3$ be finite with $|s|\ge K(8m+5)^3$. Then there is $t\subseteq s$ with $|t|=K$ whose distinct points are far apart in some coordinate:
--   $$
--   a\ne b\in t\ \Longrightarrow\ \exists i:\ |a_i-b_i|>4m+2 .
--   $$
--
--   Well-separated entrants have disjoint seed trials.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/BoxGeometry.lean#L196-L247

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical

theorem OAI.CriticalZ3.Box.separated_subset (s : Finset Vertex) (m K : ℕ)
    (hcard : K*(8*m+5)^3 ≤ s.card) :
    ∃ t ⊆ s, t.card = K ∧
      ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ∃ i, (4*m+2 : ℤ) < |a i-b i| := by sorry
