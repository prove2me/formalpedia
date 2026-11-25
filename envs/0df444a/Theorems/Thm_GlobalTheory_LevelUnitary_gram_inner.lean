-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnitary_gram_inner
-- name    : GlobalTheory.LevelUnitary.gram_inner
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:24:19.575864+00:00
-- url     : https://prove2.me/theorems/8d346b37-6cf7-5f4f-bd39-f355d2cdd228
-- title:
--   Level Unitary: gram inner
-- statement:
--   The Level Unitary construction uses the gram inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramRight.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramRight.lean#L51-L59

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.LevelUnitary
variable (k i r' : ℕ)

theorem GlobalTheory.LevelUnitary.gram_inner : (incl k i r')ᴴ * Hpk k (i + r') * incl k i r' = Hpk k r' := by sorry
