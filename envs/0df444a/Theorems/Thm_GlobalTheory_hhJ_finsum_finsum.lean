-- Prove2me | Theorems.Thm_GlobalTheory_hhJ_finsum_finsum
-- name    : GlobalTheory.hhJ_finsum_finsum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:59.197419+00:00
-- url     : https://prove2.me/theorems/6b94fca3-14c6-4e40-99c3-9d1ac9cbd56f
-- title:
--   Global Theory: hh J finsum finsum
-- statement:
--   The Global Theory construction uses the hh J finsum finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumNormHhJSelfLe.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumNormHhJSelfLe.lean#L26-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormHhJSelfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}

theorem GlobalTheory.hhJ_finsum_finsum {ι : Type} (ε : Fin n → Bool) (y : ι → Fin n → M) (In : Finset ι) :
    hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, ∑ t ∈ In, hhJ ε (y s) (y t) := by sorry
