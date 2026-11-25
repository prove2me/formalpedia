-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZetaValueIdeals_IsZetaValues_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsZetaValues.unique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:09.01347+00:00
-- url     : https://prove2.me/theorems/40fabc4e-4e03-530c-96fe-3e0e54dc5d58
-- title:
--   Is Zeta Values: unique
-- statement:
--   The Is Zeta Values construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L64-L74

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsZetaValues.unique {k : ℕ} (hk : 1 ≤ k) {z z' : ClassGroup (𝓞 F) → ℚ} (h : IsZetaValues k z)
    (h' : IsZetaValues k z') : z = z' := by sorry
