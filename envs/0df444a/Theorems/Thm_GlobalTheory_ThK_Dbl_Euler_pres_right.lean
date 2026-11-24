-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Euler_pres_right
-- name    : GlobalTheory.ThK.Dbl.Euler.pres_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:03:07.282034+00:00
-- url     : https://prove2.me/theorems/80555984-ba7a-4349-8af6-7a912e6cf2fc
-- title:
--   Euler: pres right
-- statement:
--   The Euler construction uses the pres right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/EulerA.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/EulerA.lean#L12-L20

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_EulerA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Euler
open MeasureTheory Set
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H] [SecondCountableTopology H] {ν : Measure H} [ν.IsHaarMeasure] {K : Subgroup H}

theorem GlobalTheory.ThK.Dbl.Euler.pres_right (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) {k : H} (hk : k ∈ K) :
    MeasurePreserving (· * k) ν ν := by sorry
