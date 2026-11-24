-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Bernstein_positionOne_invariantIntegral_exchange_step
-- name    : GlobalTheory.CompanionTheory.Bernstein.positionOne_invariantIntegral_exchange_step
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:21:16.268876+00:00
-- url     : https://prove2.me/theorems/b3643862-58e7-45fa-a319-670898fb6cdd
-- title:
--   Bernstein: position One invariant Integral exchange step
-- statement:
--   The Bernstein construction uses the position One invariant Integral exchange step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementCommutative.lean#L57-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementCommutative.lean#L57-L159

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementCommutative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bernstein

theorem GlobalTheory.CompanionTheory.Bernstein.positionOne_invariantIntegral_exchange_step (l N K : ℕ) (hN : 0 < N)
    (hK : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin l → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) →
      4 * N ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin (l + 1) → Module.End ℂ V), Module.finrank ℂ V = n → (∀ i j, Commute (a i) (a j)) →
      N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V := by sorry
