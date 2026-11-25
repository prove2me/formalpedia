-- Prove2me | Theorems.Thm_GlobalTheory_T_local_density_bound_near_point
-- name    : GlobalTheory.T.local_density_bound_near_point
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:51.346907+00:00
-- url     : https://prove2.me/theorems/27b0e845-be32-4f7f-a145-4da433960c55
-- title:
--   T: local density bound near point
-- statement:
--   The T construction uses the local density bound near point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalDensityBoundNearPointStatement.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalDensityBoundNearPointStatement.lean#L8-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.local_density_bound_near_point : ∀ (d : ℕ) (T : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1))) (ρ : ReciprocityTheory.L2DbarEstimates.V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : ReciprocityTheory.L2DbarEstimates.V (d + 1)),
    IsOpen T → z₀ ∈ T → ContinuousOn ρ T → ContinuousOn (fun z => G (GlobalTheory.LineCos.base z)) T →
    (∀ z ∈ T, (G (GlobalTheory.LineCos.base z)).PosDef) →
    ∃ N : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by sorry
