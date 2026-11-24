-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_inv_mem_low
-- name    : GlobalTheory.CompanionTheory.Iwahori.UpInv.inv_mem_low
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:45.604807+00:00
-- url     : https://prove2.me/theorems/ac438866-e963-4e3b-a917-6dce25ccee0f
-- title:
--   Up Inv: inv mem low
-- statement:
--   The Up Inv construction uses the inv mem low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UpperTriangularInverseIsUpper.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UpperTriangularInverseIsUpper.lean#L43-L50

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.UpInv
variable {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [Fintype ι]

theorem GlobalTheory.CompanionTheory.Iwahori.UpInv.inv_mem_low [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) {m : ℕ} {x : V} (hx : x ∈ low wt P m) : a' x ∈ low wt P m := by sorry
