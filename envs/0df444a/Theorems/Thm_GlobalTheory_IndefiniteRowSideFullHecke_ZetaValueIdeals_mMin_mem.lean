-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZetaValueIdeals_mMin_mem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.mMin_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:56.578059+00:00
-- url     : https://prove2.me/theorems/617a21ee-2eff-43ea-9bcd-a69334053d78
-- title:
--   Zeta Value Ideals: m Min mem
-- statement:
--   The Zeta Value Ideals construction uses the m Min mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L76-L78

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.mMin_mem {l : ℕ} (hl : 1 ≤ l) (n : ℕ) : ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ mMin l n = padicValNat l (a ^ n - 1) := by sorry
