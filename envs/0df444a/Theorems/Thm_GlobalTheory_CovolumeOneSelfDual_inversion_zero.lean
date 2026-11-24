-- Prove2me | Theorems.Thm_GlobalTheory_CovolumeOneSelfDual_inversion_zero
-- name    : GlobalTheory.CovolumeOneSelfDual.inversion_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:44:27.327209+00:00
-- url     : https://prove2.me/theorems/b2adb9f4-18f8-49c2-8c53-cce7642ef314
-- title:
--   Covolume One Self Dual: inversion zero
-- statement:
--   The Covolume One Self Dual construction uses the inversion zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SelfDualOfCovolumeOne.lean#L106-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SelfDualOfCovolumeOne.lean#L106-L161

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SelfDualOfCovolumeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.CovolumeOneSelfDual
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : G → G → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure G) (𝓕 : Set G) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)
include hK hcov hc hsy hadd hn hker hinj hμ hF h1

theorem GlobalTheory.CovolumeOneSelfDual.inversion_zero {Φ : G → ℂ} (hΦ : Continuous Φ) (hs : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * B x y ∂μ) μ) :
    ∫ y, (∫ x, Φ x * B x y ∂μ) ∂μ = Φ 0 := by sorry
