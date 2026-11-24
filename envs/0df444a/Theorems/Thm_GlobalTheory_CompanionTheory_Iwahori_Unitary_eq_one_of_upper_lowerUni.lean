-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_eq_one_of_upper_lowerUni
-- name    : GlobalTheory.CompanionTheory.Iwahori.Unitary.eq_one_of_upper_lowerUni
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:26.43186+00:00
-- url     : https://prove2.me/theorems/a8f9c5f6-0c5c-4c71-8d38-247ff598a623
-- title:
--   Unitary: eq one of upper lower Uni
-- statement:
--   The Unitary construction uses the eq one of upper lower Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L63-L75

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

theorem GlobalTheory.CompanionTheory.Iwahori.Unitary.eq_one_of_upper_lowerUni {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P)
    (hw : Function.Injective wt) {c : E} (hu : IsUpper wt P c) (hl : IsLowerUni wt P c) :
    c = 1 := by sorry
