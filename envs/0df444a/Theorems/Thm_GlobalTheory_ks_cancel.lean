-- Prove2me | Theorems.Thm_GlobalTheory_ks_cancel
-- name    : GlobalTheory.ks_cancel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:44.526435+00:00
-- url     : https://prove2.me/theorems/e7d630e8-f1b3-459f-9e34-f191bdab373a
-- title:
--   Global Theory: ks cancel
-- statement:
--   The Global Theory construction uses the ks cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelArtinianNoetherianSummand.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelArtinianNoetherianSummand.lean#L40-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismIndecomposableNilpotentOrBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.ks_cancel : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by sorry
