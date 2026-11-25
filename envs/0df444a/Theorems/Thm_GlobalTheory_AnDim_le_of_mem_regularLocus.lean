-- Prove2me | Theorems.Thm_GlobalTheory_AnDim_le_of_mem_regularLocus
-- name    : GlobalTheory.AnDim.le_of_mem_regularLocus
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:44.976879+00:00
-- url     : https://prove2.me/theorems/1e623a3b-0b2c-4d8f-9171-e9b65dd0a931
-- title:
--   An Dim: le of mem regular Locus
-- statement:
--   The An Dim construction uses the le of mem regular Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L126-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L126-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.AnDim.le_of_mem_regularLocus {A : FinHolAtlas d X} {T : Set X} {n k : ℕ}
    {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → X} {j : Fin A.n} (hU : IsOpen U)
    (hmaps : Set.MapsTo g U (T ∩ (A.chart j).source)) (han : AnalyticOnNhd ℂ (A.chart j ∘ g) U)
    {z : Fin k → ℂ} (hz : z ∈ U) (hinj : Function.Injective (fderiv ℂ (A.chart j ∘ g) z))
    (hreg : g z ∈ regularLocus A T n) : k ≤ n := by sorry
