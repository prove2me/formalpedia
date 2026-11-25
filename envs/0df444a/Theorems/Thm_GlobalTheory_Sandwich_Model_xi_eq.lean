-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_Model_xi_eq
-- name    : GlobalTheory.Sandwich.Model.xi_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:06.682035+00:00
-- url     : https://prove2.me/theorems/000b0778-7111-4ab5-8f15-df469ecbbff7
-- title:
--   Model: xi eq
-- statement:
--   The Model construction uses the xi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L14-L14

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

theorem GlobalTheory.Sandwich.Model.xi_eq (ε : PreTilt O p) : xi ε = ReciprocityTheory.PGsh.Ainf.xi p O ε := by sorry
