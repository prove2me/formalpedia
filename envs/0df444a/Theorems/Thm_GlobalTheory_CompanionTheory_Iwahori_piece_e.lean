-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_e
-- name    : GlobalTheory.CompanionTheory.Iwahori.piece_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:28.259935+00:00
-- url     : https://prove2.me/theorems/496fd214-4142-4a67-b420-bde35f7b74de
-- title:
--   Iwahori: piece e
-- statement:
--   The Iwahori construction uses the piece e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L76-L83

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

theorem GlobalTheory.CompanionTheory.Iwahori.piece_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (e j) = if i = some (Sum.inl j) then e j else 0 := by sorry
