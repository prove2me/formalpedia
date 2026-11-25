-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_vHalf_left_inv_and_mul
-- name    : GlobalTheory.HCXi.vHalf_left_inv_and_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:22.2958+00:00
-- url     : https://prove2.me/theorems/efcb9246-555f-416b-bf5b-618c1a04b439
-- title:
--   HCXi: v Half left inv and mul
-- statement:
--   The HCXi construction uses the v Half left inv and mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L37-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariant
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
open GlobalTheory GlobalTheory.HCXi

theorem GlobalTheory.HCXi.vHalf_left_inv_and_mul : ∀ k r : ℕ, 1 ≤ k →
    (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧
    ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by sorry
