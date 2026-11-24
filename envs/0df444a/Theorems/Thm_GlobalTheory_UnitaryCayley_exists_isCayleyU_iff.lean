-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryCayley_exists_isCayleyU_iff
-- name    : GlobalTheory.UnitaryCayley.exists_isCayleyU_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:14.557701+00:00
-- url     : https://prove2.me/theorems/20e46d51-ef17-48d7-add8-eb8bf4928271
-- title:
--   Unitary Cayley: exists is Cayley U iff
-- statement:
--   The Unitary Cayley construction uses the exists is Cayley U iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsIsCayleyUIff.lean#L110-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsIsCayleyUIff.lean#L110-L125

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

theorem GlobalTheory.UnitaryCayley.exists_isCayleyU_iff (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) :
    (∃ P, IsCayleyU k r ε P) ↔ (univ.filter fun i => ε i = true).card = k + r := by sorry
