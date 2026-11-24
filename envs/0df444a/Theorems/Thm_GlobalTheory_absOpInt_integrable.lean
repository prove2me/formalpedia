-- Prove2me | Theorems.Thm_GlobalTheory_absOpInt_integrable
-- name    : GlobalTheory.absOpInt_integrable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:14.065356+00:00
-- url     : https://prove2.me/theorems/558c165c-1dcd-465d-b9c7-0f1ea7db702c
-- title:
--   Global Theory: abs Op Int integrable
-- statement:
--   The Global Theory construction uses the abs Op Int integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsOpIntIntegrable.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsOpIntIntegrable.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsOpIntIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.absOpInt_integrable {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => π g x) (φ : G → ℂ) (hφ : Integrable φ μ) (y : Hp) :
    Integrable (fun g => φ g • π g y) μ := by sorry
