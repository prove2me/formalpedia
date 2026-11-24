-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_lowerUni_of_inv
-- name    : GlobalTheory.CompanionTheory.Iwahori.Unitary.lowerUni_of_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:17.89125+00:00
-- url     : https://prove2.me/theorems/87771499-c384-4073-b40a-29d84a786324
-- title:
--   Unitary: lower Uni of inv
-- statement:
--   The Unitary construction uses the lower Uni of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L54-L61

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Unitary
variable {E ι : Type} [Ring E] [Fintype ι]

theorem GlobalTheory.CompanionTheory.Iwahori.Unitary.lowerUni_of_inv {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {b b' : E} (hb : IsLowerUni wt P b) (hb' : IsLower wt P b') (h : b * b' = 1) :
    IsLowerUni wt P b' := by sorry
