-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryCayley_transport
-- name    : GlobalTheory.UnitaryCayley.transport
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:01.716285+00:00
-- url     : https://prove2.me/theorems/74d2e291-11ea-4ae5-a863-1e8c6c70e53e
-- title:
--   Unitary Cayley: transport
-- statement:
--   The Unitary Cayley construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsIsCayleyUIff.lean#L127-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsIsCayleyUIff.lean#L127-L161

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley

theorem GlobalTheory.UnitaryCayley.transport {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : IsCayleyU k r ε P)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (P⁻¹ * g * P ∈ UH (Hpk k r) ↔ g ∈ UJset ε) ∧
    (P⁻¹ * g * P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ ↔
      g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) := by sorry
