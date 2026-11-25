-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_VLev_gram_succ
-- name    : GlobalTheory.HCXi.VLev.gram_succ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:47:08.086854+00:00
-- url     : https://prove2.me/theorems/c081ea44-f77a-4756-baab-4c9b7c46ed24
-- title:
--   VLev: gram succ
-- statement:
--   The VLev construction uses the gram succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L120-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L120-L133

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

theorem GlobalTheory.HCXi.VLev.gram_succ (j : Fin (1 + r' + 1)) (b : Fin (r' + 1)) (hj : j.val = b.val + 1) :
    gram k (1 + r') M j = Complex.normSq a * gram k r' h b := by sorry
