-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_Model_mem_mixed_Fil
-- name    : GlobalTheory.Sandwich.Model.mem_mixed_Fil
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:40.702067+00:00
-- url     : https://prove2.me/theorems/1a99a440-d0a2-4ad0-ae98-e537ed5bd1ca
-- title:
--   Model: mem mixed Fil
-- statement:
--   The Model construction uses the mem mixed Fil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L49-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem GlobalTheory.Sandwich.Model.mem_mixed_Fil (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ)
    (S : Finset (Fin h)) (x : Fin h → O) : x ∈ (mixed ε h S).Fil ↔ ∀ i ∈ S, x i = 0 := by sorry
