-- Prove2me | Theorems.Thm_GlobalTheory_relLength_sup_ne_top_iff
-- name    : GlobalTheory.relLength_sup_ne_top_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:30.043808+00:00
-- url     : https://prove2.me/theorems/52c491d4-6836-4801-b978-78fa8e9419d1
-- title:
--   Global Theory: rel Length sup ne top iff
-- statement:
--   The Global Theory construction uses the rel Length sup ne top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L72-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem GlobalTheory.relLength_sup_ne_top_iff {A B C : Submodule R V} :
    relLength (A ⊔ B) C ≠ ⊤ ↔ relLength A C ≠ ⊤ ∧ relLength B C ≠ ⊤ := by sorry
