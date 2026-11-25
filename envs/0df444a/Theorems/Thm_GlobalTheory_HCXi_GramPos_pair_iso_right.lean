-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_GramPos_pair_iso_right
-- name    : GlobalTheory.HCXi.GramPos.pair_iso_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:09:56.846689+00:00
-- url     : https://prove2.me/theorems/68aaf6f0-3e08-46cd-96f6-81f5e5f08920
-- title:
--   Gram Pos: pair iso right
-- statement:
--   The Gram Pos construction uses the pair iso right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramPositiveVolumeContinuous.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramPositiveVolumeContinuous.lean#L31-L35

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

theorem GlobalTheory.HCXi.GramPos.pair_iso_right (k r : ℕ) (M : Mat k r) (v) :
    star v ⬝ᵥ M *ᵥ isoVec k r =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ M *ᵥ bvec (wI k r 0) + star v ⬝ᵥ M *ᵥ bvec (wI k r (Fin.last k))) := by sorry
