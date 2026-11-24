-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_isLowerUni_one
-- name    : GlobalTheory.CompanionTheory.Iwahori.Gauss.isLowerUni_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:42.894856+00:00
-- url     : https://prove2.me/theorems/98a4a360-1641-4a1b-94fb-d7c2c343d802
-- title:
--   Gauss: is Lower Uni one
-- statement:
--   The Gauss construction uses the is Lower Uni one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L64-L68

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

theorem GlobalTheory.CompanionTheory.Iwahori.Gauss.isLowerUni_one (hP : IsPieces P) : IsLowerUni wt P 1 := by sorry
