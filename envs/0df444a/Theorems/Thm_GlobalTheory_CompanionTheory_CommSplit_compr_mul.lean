-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_mul
-- name    : GlobalTheory.CompanionTheory.CommSplit.compr_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:01.022825+00:00
-- url     : https://prove2.me/theorems/171101f1-d56c-4d35-9cb6-2366cd36ca47
-- title:
--   Comm Split: compr mul
-- statement:
--   The Comm Split construction uses the compr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L26-L31

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommSplit
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CommSplit.compr_mul (W W' : Submodule ℂ V) (hc : IsCompl W W') (b c : End ℂ V)
    (hcW : ∀ w ∈ W, c w ∈ W) :
    compr W W' hc (b * c) = compr W W' hc b * compr W W' hc c := by sorry
