-- Prove2me | Theorems.Thm_GlobalTheory_exists_countable_local_pid_subring
-- name    : GlobalTheory.exists_countable_local_pid_subring
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:33.789979+00:00
-- url     : https://prove2.me/theorems/bc34aed3-87e8-4afc-82d1-aa89706ce20f
-- title:
--   Global Theory: exists countable local pid subring
-- statement:
--   The Global Theory construction uses the exists countable local pid subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCountableLocalPidSubring.lean#L5-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCountableLocalPidSubring.lean#L5-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCountableLocalPidSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_countable_local_pid_subring (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] (S : Set R) (hS : S.Countable) :
    ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀),
      Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R := by sorry
