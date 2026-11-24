-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_An_at_value
-- name    : GlobalTheory.ThK.Dbl.An.at_value
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:54.917573+00:00
-- url     : https://prove2.me/theorems/72e94492-bffa-435c-bedc-d1d8f467c20d
-- title:
--   An: at value
-- statement:
--   The An construction uses the at value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L34-L47

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FarRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
variable {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (ν : Measure G) [IsFiniteMeasure ν] (ρ : Measure H) [IsFiniteMeasure ρ] {φ : G → ℂ}

theorem GlobalTheory.ThK.Dbl.An.at_value {θ : H × G → ℂ} (hθ : BC θ) (hφ : BC φ) :
    ∫ y, (∫ g, θ (g, y.1) * star (θ (g, y.2)) ∂ρ) * (φ y.2 * star (φ y.1)) ∂ν.prod ν =
      ∫ g, (∫ h, φ h * star (θ (g, h)) ∂ν) * star (∫ h, φ h * star (θ (g, h)) ∂ν) ∂ρ := by sorry
