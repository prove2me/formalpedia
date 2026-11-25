-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_Funct_inner
-- name    : GlobalTheory.HCXi.Funct.inner
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:21.946342+00:00
-- url     : https://prove2.me/theorems/e77e75f5-9b6b-5e49-9629-9bacb3a13d54
-- title:
--   Funct: inner
-- statement:
--   The Funct construction uses the inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SphericalFunctionFunctionalEq.lean#L30-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SphericalFunctionFunctionalEq.lean#L30-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuousStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SphericalFunctionFunctionalEq
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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.Funct

theorem GlobalTheory.HCXi.Funct.inner {k r : ℕ} (μK : Measure (Mt k r)) (hk : 1 ≤ k) (hμ : IsKMeas k r μK) {x : Mat k r} (hx : x ∈ GV k r)
    {g : Mat k r} (hg : g ∈ GV k r) :
    (∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * Matrix.of κ * g)) ∂μK)
      = XiE k r μK x * ENNReal.ofReal (vHalf k r g) := by sorry
