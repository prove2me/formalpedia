-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_isLowerUni_mul
-- name    : GlobalTheory.CompanionTheory.Iwahori.Gauss.isLowerUni_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:59.622149+00:00
-- url     : https://prove2.me/theorems/614a765a-5ddc-46e5-8c05-5ad5ae5488e6
-- title:
--   Gauss: is Lower Uni mul
-- statement:
--   The Gauss construction uses the is Lower Uni mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L43-L58

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

theorem GlobalTheory.CompanionTheory.Iwahori.Gauss.isLowerUni_mul (hwt : Function.Injective wt) (hP : IsPieces P) {a b : E}
    (ha : IsLowerUni wt P a) (hb : IsLowerUni wt P b) : IsLowerUni wt P (a * b) := by sorry
