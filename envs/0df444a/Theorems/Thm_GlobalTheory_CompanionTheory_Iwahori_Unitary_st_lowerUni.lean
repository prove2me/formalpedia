-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_st_lowerUni
-- name    : GlobalTheory.CompanionTheory.Iwahori.Unitary.st_lowerUni
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:17.604916+00:00
-- url     : https://prove2.me/theorems/24c60535-e1ae-495a-aef3-5a102a08ea3d
-- title:
--   Unitary: st lower Uni
-- statement:
--   The Unitary construction uses the st lower Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L98-L104

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
variable {wt : ι → ℕ} {P : ι → E} {rev : ι → ι} {st : E → E}

theorem GlobalTheory.CompanionTheory.Iwahori.Unitary.st_lowerUni (hrev : ∀ i, rev (rev i) = i)
    (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLowerUni wt P x) :
    IsLowerUni wt P (st x) := by sorry
