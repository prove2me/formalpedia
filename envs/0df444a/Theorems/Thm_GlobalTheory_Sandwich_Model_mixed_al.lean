-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_Model_mixed_al
-- name    : GlobalTheory.Sandwich.Model.mixed_al
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:46.253391+00:00
-- url     : https://prove2.me/theorems/67403f10-4370-41f9-ab3f-61c7c20bb392
-- title:
--   Model: mixed al
-- statement:
--   The Model construction uses the mixed al property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L39-L42

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

theorem GlobalTheory.Sandwich.Model.mixed_al (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ) (S : Finset (Fin h))
    (x : Fin h → O) (i : Fin h) : (mixed ε h S).al x i = if i ∈ S then 0 else x i := by sorry
