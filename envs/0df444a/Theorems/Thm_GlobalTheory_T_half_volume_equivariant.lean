-- Prove2me | Theorems.Thm_GlobalTheory_T_half_volume_equivariant
-- name    : GlobalTheory.T.half_volume_equivariant
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:12:26.854787+00:00
-- url     : https://prove2.me/theorems/bd8c89d3-e8c1-58b5-a6cf-8f6a84dca2ec
-- title:
--   T: half volume equivariant
-- statement:
--   The T construction uses the half volume equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariantStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariantStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.half_volume_equivariant : ∀ k r : ℕ, 1 ≤ k → (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧ ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by sorry
