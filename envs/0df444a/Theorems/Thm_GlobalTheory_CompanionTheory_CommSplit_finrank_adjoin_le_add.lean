-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_finrank_adjoin_le_add
-- name    : GlobalTheory.CompanionTheory.CommSplit.finrank_adjoin_le_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:07.16027+00:00
-- url     : https://prove2.me/theorems/964bf862-c414-449f-8108-9ac95cf95290
-- title:
--   Comm Split: finrank adjoin le add
-- statement:
--   The Comm Split construction uses the finrank adjoin le add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L71-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L71-L112

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

theorem GlobalTheory.CompanionTheory.CommSplit.finrank_adjoin_le_add :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
      (a : Fin l → Module.End ℂ V) (W W' : Submodule ℂ V), IsCompl W W' →
      ∀ (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (h' : ∀ i, ∀ w ∈ W', a i w ∈ W'),
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h i) : Module.End ℂ W))) +
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h' i) : Module.End ℂ W'))) := by sorry
