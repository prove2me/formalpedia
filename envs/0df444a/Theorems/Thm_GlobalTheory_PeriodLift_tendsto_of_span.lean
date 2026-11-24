-- Prove2me | Theorems.Thm_GlobalTheory_PeriodLift_tendsto_of_span
-- name    : GlobalTheory.PeriodLift.tendsto_of_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:59.119373+00:00
-- url     : https://prove2.me/theorems/48b782ee-0cf2-4e2b-b630-87671684e24b
-- title:
--   Period Lift: tendsto of span
-- statement:
--   The Period Lift construction uses the tendsto of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PeriodCoordinatesFramesLiftTendsto.lean#L70-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PeriodCoordinatesFramesLiftTendsto.lean#L70-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PeriodCoordinatesFramesLiftTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.PeriodLift

theorem GlobalTheory.PeriodLift.tendsto_of_span {E : Type} [Field E] {r : ℕ} {ι : Type} {𝓕 : Filter ι}
    (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ : ι → (Fin r → E) → ℂ) (Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ n v w, Φ n (v + w) = Φ n v + Φ n w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ n (c : E) v, Φ n (c • v) = σ c * Φ n v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0)
    (h : ∀ v ∈ S, Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v))) (v : Fin r → E) :
    Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v)) := by sorry
