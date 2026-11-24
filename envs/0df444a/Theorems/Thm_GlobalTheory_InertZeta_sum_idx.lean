-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_sum_idx
-- name    : GlobalTheory.InertZeta.sum_idx
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:26:37.575327+00:00
-- url     : https://prove2.me/theorems/44ddfa1d-5517-46aa-b6e6-db5115382ba9
-- title:
--   Inert Zeta: sum idx
-- statement:
--   The Inert Zeta construction uses the sum idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L194-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L194-L197

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.InertZeta.sum_idx {M : Type} [AddCommMonoid M] (f : Fin (N + 2) → M) :
    ∑ i, f i = f 0 + ∑ j, f (mid j) + f (Fin.last (N + 1)) := by sorry
