-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_st_block
-- name    : GlobalTheory.CompanionTheory.Iwahori.Unitary.st_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:32.430239+00:00
-- url     : https://prove2.me/theorems/2dc3bb8d-11aa-44bd-855b-b3c8efd0c906
-- title:
--   Unitary: st block
-- statement:
--   The Unitary construction uses the st block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntiInvolutionSwapsUpperLower.lean#L81-L84

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

theorem GlobalTheory.CompanionTheory.Iwahori.Unitary.st_block (hrev : ∀ i, rev (rev i) = i) (hmul : ∀ a b, st (a * b) = st b * st a)
    (hst : ∀ i, st (P i) = P (rev i)) (x : E) (i j : ι) :
    P i * st x * P j = st (P (rev j) * x * P (rev i)) := by sorry
