-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_Model_mixed_bb
-- name    : GlobalTheory.Sandwich.Model.mixed_bb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:57:24.506156+00:00
-- url     : https://prove2.me/theorems/25725e7a-8811-5037-94db-36f0ae435914
-- title:
--   Model: mixed bb
-- statement:
--   The Model construction uses the mixed bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L44-L47

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

theorem GlobalTheory.Sandwich.Model.mixed_bb (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ) (S : Finset (Fin h))
    (x : Fin h → O) (i : Fin h) : (mixed ε h S).bb x i = if i ∈ S then x i else 0 := by sorry
