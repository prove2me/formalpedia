-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_An_far_right
-- name    : GlobalTheory.ThK.Dbl.An.far_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:23.049461+00:00
-- url     : https://prove2.me/theorems/8c4c7bb9-96ba-47fd-92c6-56125c563f0e
-- title:
--   An: far right
-- statement:
--   The An construction uses the far right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L49-L57

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

theorem GlobalTheory.ThK.Dbl.An.far_right [Group G] [ContinuousMul G] (μ : Measure G) [SFinite μ] {k : G × G → ℂ} {w : G → ℂ} (hk : BC k) (hφ : BC φ)
    (hw : Integrable w μ) (h : ∀ h, ∫ h', k (h, h') * φ h' ∂ν = ∫ g, w g * φ (h * g) ∂μ) :
    ∫ y, k y * (φ y.2 * star (φ y.1)) ∂ν.prod ν = ∫ g, w g * ∫ h, φ (h * g) * star (φ h) ∂ν ∂μ := by sorry
