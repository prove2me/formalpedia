-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_isPieces_piece
-- name    : GlobalTheory.CompanionTheory.Iwahori.isPieces_piece
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:26.383548+00:00
-- url     : https://prove2.me/theorems/9ad21f31-7b11-4a24-921f-884875c3b30f
-- title:
--   Iwahori: is Pieces piece
-- statement:
--   The Iwahori construction uses the is Pieces piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L107-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L107-L129

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

theorem GlobalTheory.CompanionTheory.Iwahori.isPieces_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) :
    IsPieces (piece hh δ e f) := by sorry
