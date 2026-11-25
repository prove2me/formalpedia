-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_VLev_vHalf_block
-- name    : GlobalTheory.HCXi.VLev.vHalf_block
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:00.206328+00:00
-- url     : https://prove2.me/theorems/4623405b-72e5-4fde-80be-a347e1daa039
-- title:
--   VLev: v Half block
-- statement:
--   The VLev construction uses the v Half block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L135-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L135-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
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
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev
variable {k r' : ℕ} (M : Mat k (1 + r')) (h : Mat k r') (a : ℂ) (hM0 : M *ᵥ e0 k r' = a • e0 k r')
  (hM : ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, M *ᵥ liftVec k 1 r' w = liftVec k 1 r' (h *ᵥ w) + c • e0 k r')
include hM0
include hM

theorem GlobalTheory.HCXi.VLev.vHalf_block (ha : a ≠ 0) : vHalf k (1 + r') M =
    Complex.normSq a ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' h := by sorry
