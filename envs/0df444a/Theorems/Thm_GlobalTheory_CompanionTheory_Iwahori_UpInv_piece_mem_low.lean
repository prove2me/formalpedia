-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_piece_mem_low
-- name    : GlobalTheory.CompanionTheory.Iwahori.UpInv.piece_mem_low
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:44.219598+00:00
-- url     : https://prove2.me/theorems/2822a176-ad92-4eda-b2a7-4a7bf2de6552
-- title:
--   Up Inv: piece mem low
-- statement:
--   The Up Inv construction uses the piece mem low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UpperTriangularInverseIsUpper.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UpperTriangularInverseIsUpper.lean#L52-L59

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

theorem GlobalTheory.CompanionTheory.Iwahori.UpInv.piece_mem_low {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P) (j : ι) (x : V) :
    P j x ∈ low wt P (wt j + 1) := by sorry
