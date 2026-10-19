-- Prove2me | Theorems.Thm_OAI_FiniteTrails_exists_cycle_nonzero
-- name    : OAI.FiniteTrails.exists_cycle_nonzero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:39:57.445099+00:00
-- url     : https://prove2.me/theorems/817032ba-020d-40f4-b74e-35a5d9075ba9
-- title:
--   A nonzero total weight has a cycle of nonzero weight
-- statement:
--   Let $\sigma$ be a permutation of a finite set $D$ and $w:D\to\mathbb Z$ with $\sum_dw(d)\ne0$. Then some cycle of $\sigma$ has nonzero total weight:
--   $$
--   \exists d:\ \sum_{e\sim_\sigma d}w(e)\ne0 .
--   $$
--
--   It is used to extract a contour with nonzero winding from a boundary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/FiniteTrails.lean#L29-L54

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
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails

open OAI OAI.FiniteTrails
universe uD uV
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Classical Function
variable {D : Type uD} {V : Type uV} [Fintype D]

theorem OAI.FiniteTrails.exists_cycle_nonzero (σ : Equiv.Perm D) (w : D → ℤ)
    (hw : ∑ d, w d ≠ 0) :
    ∃ d, (∑ e : D, if σ.SameCycle d e then w e else 0) ≠ 0 := by sorry
