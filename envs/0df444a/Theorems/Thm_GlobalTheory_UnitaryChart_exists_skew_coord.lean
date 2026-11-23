-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryChart_exists_skew_coord
-- name    : GlobalTheory.UnitaryChart.exists_skew_coord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:36.549904+00:00
-- url     : https://prove2.me/theorems/49bfb713-b564-4d43-81ae-355ebbab53f3
-- title:
--   Unitary Chart: exists skew coord
-- statement:
--   The Unitary Chart construction uses the exists skew coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L73-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L73-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter

theorem GlobalTheory.UnitaryChart.exists_skew_coord {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) {N : ℕ} (e : Fin N → E) (hσ : ∀ a, σ (σ a) = a)
    (hli : LinearIndependent ℝ e) (he : ∀ i, σ (e i) = -e i)
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) :
    ∃ P : E →L[ℝ] (Fin N → ℝ), (∀ t : Fin N → ℝ, P (∑ i, t i • e i) = t) ∧
      (∀ m, σ m = m → P m = 0) ∧ ∀ u v, P u = P v → u - σ u = v - σ v := by sorry
