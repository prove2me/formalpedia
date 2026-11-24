-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Bernstein_adjoin_shift
-- name    : GlobalTheory.CompanionTheory.Bernstein.adjoin_shift
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:21:45.551816+00:00
-- url     : https://prove2.me/theorems/df1c7690-2ba0-4143-b1eb-8e22568599e7
-- title:
--   Bernstein: adjoin shift
-- statement:
--   The Bernstein construction uses the adjoin shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementCommutative.lean#L34-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementCommutative.lean#L34-L55

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

theorem GlobalTheory.CompanionTheory.Bernstein.adjoin_shift {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (μ : ℂ) :
    Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ) (fun i : Fin l => a i.succ) :
      Fin (l + 1) → Module.End ℂ V)) = Algebra.adjoin ℂ (Set.range a) := by sorry
