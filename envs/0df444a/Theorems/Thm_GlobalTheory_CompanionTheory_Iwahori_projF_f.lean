-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_f
-- name    : GlobalTheory.CompanionTheory.Iwahori.projF_f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:05.344868+00:00
-- url     : https://prove2.me/theorems/653df466-cc08-4741-8ce0-2cff7e4160fe
-- title:
--   Iwahori: proj F f
-- statement:
--   The Iwahori construction uses the proj F f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L65-L70

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori
variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem GlobalTheory.CompanionTheory.Iwahori.projF_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (f j) = if j = i then f i else 0 := by sorry
