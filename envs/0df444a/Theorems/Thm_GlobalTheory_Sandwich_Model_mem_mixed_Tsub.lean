-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_Model_mem_mixed_Tsub
-- name    : GlobalTheory.Sandwich.Model.mem_mixed_Tsub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:49:50.130577+00:00
-- url     : https://prove2.me/theorems/8d63addf-3101-56bf-b56e-54e83da1afed
-- title:
--   Model: mem mixed Tsub
-- statement:
--   The Model construction uses the mem mixed Tsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L69-L80

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

theorem GlobalTheory.Sandwich.Model.mem_mixed_Tsub (ε : PreTilt O p) (h : ℕ) (S : Finset (Fin h)) (i : Fin h) (x : Fin h → O) :
    x ∈ (mixed ε h S).Tsub ((padicToO p O).comp (Pi.evalRingHom _ i)) ↔ ∀ j ≠ i, x j = 0 := by sorry
