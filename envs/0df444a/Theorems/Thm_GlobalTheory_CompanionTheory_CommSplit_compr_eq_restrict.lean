-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_eq_restrict
-- name    : GlobalTheory.CompanionTheory.CommSplit.compr_eq_restrict
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:31.426985+00:00
-- url     : https://prove2.me/theorems/cd890c9d-d15f-4796-8dfc-3e047ea16f23
-- title:
--   Comm Split: compr eq restrict
-- statement:
--   The Comm Split construction uses the compr eq restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L20-L24

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

theorem GlobalTheory.CompanionTheory.CommSplit.compr_eq_restrict (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) : compr W W' hc b = b.restrict hb := by sorry
