-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_tor_piece
-- name    : GlobalTheory.CompanionTheory.Iwahori.tor_piece
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:26.486105+00:00
-- url     : https://prove2.me/theorems/ae7ca330-61bf-4288-b4a5-2e1974e6165c
-- title:
--   Iwahori: tor piece
-- statement:
--   The Iwahori construction uses the tor piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L175-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L175-L209

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

theorem GlobalTheory.CompanionTheory.Iwahori.tor_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) {u : Fin l → L}
    {t : V ≃ₗ[L] V} (ht : IsTor s e f W u t) (i : Idx l) :
    (t.toLinearMap : Module.End L V) * piece hh δ e f i = tau s u i • piece hh δ e f i ∧
      piece hh δ e f i * (t.toLinearMap : Module.End L V) = tau s u i • piece hh δ e f i := by sorry
