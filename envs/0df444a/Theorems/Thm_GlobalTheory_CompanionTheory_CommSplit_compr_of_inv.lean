-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_of_inv
-- name    : GlobalTheory.CompanionTheory.CommSplit.compr_of_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:22.125275+00:00
-- url     : https://prove2.me/theorems/b4d2bdbc-010b-4eb0-aaa7-0d6121248750
-- title:
--   Comm Split: compr of inv
-- statement:
--   The Comm Split construction uses the compr of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L15-L18

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

theorem GlobalTheory.CompanionTheory.CommSplit.compr_of_inv (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) (w : W) : compr W W' hc b w = ⟨b w, hb w w.2⟩ := by sorry
