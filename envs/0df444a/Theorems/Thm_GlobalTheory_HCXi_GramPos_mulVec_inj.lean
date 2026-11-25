-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_GramPos_mulVec_inj
-- name    : GlobalTheory.HCXi.GramPos.mulVec_inj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:52:43.204465+00:00
-- url     : https://prove2.me/theorems/1ac4168b-18fa-4277-ad28-89d42f96ae36
-- title:
--   Gram Pos: mul Vec inj
-- statement:
--   The Gram Pos construction uses the mul Vec inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramPositiveVolumeContinuous.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramPositiveVolumeContinuous.lean#L61-L73

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

theorem GlobalTheory.HCXi.GramPos.mulVec_inj (k r : ℕ) (hk : 1 ≤ k) (g : Mat k r) (hg : g ∈ GV k r) :
    Function.Injective (g * frame k r).mulVec := by sorry
