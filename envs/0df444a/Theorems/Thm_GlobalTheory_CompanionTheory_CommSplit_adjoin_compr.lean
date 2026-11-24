-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_adjoin_compr
-- name    : GlobalTheory.CompanionTheory.CommSplit.adjoin_compr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:40.193892+00:00
-- url     : https://prove2.me/theorems/c7599726-de95-489e-994e-e0cd8071d7b6
-- title:
--   Comm Split: adjoin compr
-- statement:
--   The Comm Split construction uses the adjoin compr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L42-L69

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

theorem GlobalTheory.CompanionTheory.CommSplit.adjoin_compr {l : ℕ} (a : Fin l → End ℂ V) (W W' : Submodule ℂ V) (hc : IsCompl W W')
    (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (b : End ℂ V) (hb : b ∈ Algebra.adjoin ℂ (Set.range a)) :
    (∀ w ∈ W, b w ∈ W) ∧ compr W W' hc b ∈
      Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : End ℂ W)) := by sorry
