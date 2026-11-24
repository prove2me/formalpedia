-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Euler_factor
-- name    : GlobalTheory.ThK.Dbl.Euler.factor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:03:06.933621+00:00
-- url     : https://prove2.me/theorems/5d01737e-decb-47ae-be8f-fa1f98e54416
-- title:
--   Euler: factor
-- statement:
--   The Euler construction uses the factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/EulerA.lean#L25-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/EulerA.lean#L25-L87

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G] {μ : Measure G} [μ.IsHaarMeasure]

theorem GlobalTheory.ThK.Dbl.Euler.factor (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) (i : H →* G) (hi : Continuous i) (π : G → H) (hπ : Continuous π)
    (e : ∀ u g, π (i u * g) = u * π g) {f : G → ℂ} {l : H → ℂ} (hf : Integrable f μ)
    (hl : ∀ u g, π g = 1 → f (i u * g) = l u * f g) (hl1 : ∀ u ∈ K, l u = 1) {A : Set G} (hA : MeasurableSet A)
    (hAi : ∀ u g, i u * g ∈ A ↔ g ∈ A) : ∫ g in A, f g ∂μ = (∫ u, l u ∂ν) * ∫ g in A ∩ π ⁻¹' K, f g ∂μ := by sorry
