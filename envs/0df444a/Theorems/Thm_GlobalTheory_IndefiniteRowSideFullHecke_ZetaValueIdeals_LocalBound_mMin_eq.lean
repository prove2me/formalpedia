-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZetaValueIdeals_LocalBound_mMin_eq
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.LocalBound.mMin_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:52.602082+00:00
-- url     : https://prove2.me/theorems/68cf18d8-e1ff-42e4-bea7-813443731177
-- title:
--   Local Bound: m Min eq
-- statement:
--   The Local Bound construction uses the m Min eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L80-L86

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.LocalBound.mMin_eq {k : ℕ} {z : ClassGroup (𝓞 F) → ℚ} {l : ℕ} (h : LocalBound k z l) :
    mMin l (finrank ℚ F * k) = Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k) := by sorry
