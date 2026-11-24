-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_adj
-- name    : GlobalTheory.CompanionTheory.Iwahori.projF_adj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:09.756144+00:00
-- url     : https://prove2.me/theorems/8a96588e-ae73-4480-a05f-de18785e16d7
-- title:
--   Iwahori: proj F adj
-- statement:
--   The Iwahori construction uses the proj F adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L279-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L279-L282

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

theorem GlobalTheory.CompanionTheory.Iwahori.projF_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projF hh δ e f i x) y = h x (projE hh δ e f i y) := by sorry
