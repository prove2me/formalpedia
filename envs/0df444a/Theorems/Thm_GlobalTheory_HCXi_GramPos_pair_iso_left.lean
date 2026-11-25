-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_GramPos_pair_iso_left
-- name    : GlobalTheory.HCXi.GramPos.pair_iso_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:56:04.171534+00:00
-- url     : https://prove2.me/theorems/2f8725a8-6167-465e-8208-f66b33d0d4d7
-- title:
--   Gram Pos: pair iso left
-- statement:
--   The Gram Pos construction uses the pair iso left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramPositiveVolumeContinuous.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramPositiveVolumeContinuous.lean#L25-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.GramPos

theorem GlobalTheory.HCXi.GramPos.pair_iso_left (k r : ℕ) (M : Mat k r) (j) :
    star (isoVec k r) ⬝ᵥ M *ᵥ bvec j =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (M (wI k r 0) j + M (wI k r (Fin.last k)) j) := by sorry
