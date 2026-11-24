-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_map_low_eq
-- name    : GlobalTheory.CompanionTheory.Iwahori.UpInv.map_low_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:01.439819+00:00
-- url     : https://prove2.me/theorems/5e94f150-67dc-4cd3-8075-f6a2804c1a8d
-- title:
--   Up Inv: map low eq
-- statement:
--   The Up Inv construction uses the map low eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UpperTriangularInverseIsUpper.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UpperTriangularInverseIsUpper.lean#L36-L41

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

theorem GlobalTheory.CompanionTheory.Iwahori.UpInv.map_low_eq [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) (m : ℕ) : (low wt P m).map a = low wt P m := by sorry
