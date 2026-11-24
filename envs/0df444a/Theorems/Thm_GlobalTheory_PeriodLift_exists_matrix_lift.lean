-- Prove2me | Theorems.Thm_GlobalTheory_PeriodLift_exists_matrix_lift
-- name    : GlobalTheory.PeriodLift.exists_matrix_lift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:26.364347+00:00
-- url     : https://prove2.me/theorems/63bdd314-3f7b-4c70-a4a6-5a27b2e9b1df
-- title:
--   Period Lift: exists matrix lift
-- statement:
--   The Period Lift construction uses the exists matrix lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PeriodCoordinatesFramesLiftTendsto.lean#L8-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PeriodCoordinatesFramesLiftTendsto.lean#L8-L68

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

theorem GlobalTheory.PeriodLift.exists_matrix_lift {r : ℕ} {ι : Type} {𝓕 : Filter ι} (p : Fin r → Prop) [DecidablePred p]
    (A₀ : Matrix (Fin r) (Fin r) ℂ) (A : ι → Matrix (Fin r) (Fin r) ℂ)
    (h0 : A₀.det ≠ 0) (hA : ∀ᶠ n in 𝓕, (A n).det ≠ 0)
    (hc : ∀ a, p a → ∀ k, Tendsto (fun n => A n k a) 𝓕 (𝓝 (A₀ k a)))
    (hr : ∀ a, ¬ p a → ∀ k, Tendsto (fun n => (A n)⁻¹ a k) 𝓕 (𝓝 (A₀⁻¹ a k))) :
    ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 A₀) ∧ ∀ᶠ n in 𝓕,
      (∀ a, p a → ∀ k, B n k a = A n k a) ∧ (∀ a, ¬ p a → ∀ k, (B n)⁻¹ a k = (A n)⁻¹ a k) := by sorry
