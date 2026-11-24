-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_exists_star
-- name    : GlobalTheory.CompanionTheory.Iwahori.exists_star
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:59.125167+00:00
-- url     : https://prove2.me/theorems/8773a86e-6b05-47f2-b24b-d33095a8eef5
-- title:
--   Iwahori: exists star
-- statement:
--   The Iwahori construction uses the exists star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L297-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L297-L315

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

theorem GlobalTheory.CompanionTheory.Iwahori.exists_star (hs : IsInv s) (hh : IsHerm s h)
    (hadj : ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y)) :
    ∃ st : Module.End L V → Module.End L V, (∀ g x y, h (g x) y = h x (st g y)) ∧
      (∀ a b, st (a * b) = st b * st a) ∧ st 1 = 1 ∧ st 0 = 0 ∧
      ∀ i : Idx l, st (piece hh δ e f i) = piece hh δ e f (rev i) := by sorry
