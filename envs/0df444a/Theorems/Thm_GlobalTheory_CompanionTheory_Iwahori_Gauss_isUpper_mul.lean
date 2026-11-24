-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_isUpper_mul
-- name    : GlobalTheory.CompanionTheory.Iwahori.Gauss.isUpper_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:53.397382+00:00
-- url     : https://prove2.me/theorems/f14ab379-11fd-4775-936d-1b4c389d5e94
-- title:
--   Gauss: is Upper mul
-- statement:
--   The Gauss construction uses the is Upper mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L34-L41

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Gauss
open GlobalTheory.CompanionTheory.Iwahori
variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}

theorem GlobalTheory.CompanionTheory.Iwahori.Gauss.isUpper_mul (hP : IsPieces P) {a b : E} (ha : IsUpper wt P a) (hb : IsUpper wt P b) :
    IsUpper wt P (a * b) := by sorry
