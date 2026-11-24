-- Prove2me | Theorems.Thm_GlobalTheory_DI_delta_Dtot_props
-- name    : GlobalTheory.DI.delta_Dtot_props
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:35:33.11996+00:00
-- url     : https://prove2.me/theorems/105d0f3c-c57a-473a-b5a6-2d7282bef202
-- title:
--   DI: delta Dtot props
-- statement:
--   The DI construction uses the delta Dtot props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L73-L80

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem GlobalTheory.DI.delta_Dtot_props : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E),
    (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧
    (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧
    (∀ c : Finset ι → E, delta (delta c) = 0) ∧
    ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) := by sorry
