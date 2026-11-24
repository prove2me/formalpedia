-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_tau_mono
-- name    : GlobalTheory.CompanionTheory.Iwahori.tau_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:25.59155+00:00
-- url     : https://prove2.me/theorems/a7067bf6-e30b-4e8d-9652-bbda9e996ad3
-- title:
--   Iwahori: tau mono
-- statement:
--   The Iwahori construction uses the tau mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L232-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L232-L250

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

theorem GlobalTheory.CompanionTheory.Iwahori.tau_mono (hs : IsInv s) {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (hm : Monotone fun i => ‖u i‖)
    (h1 : ∀ i, ‖u i‖ ≤ 1) (i j : Idx l) (hij : wt i ≤ wt j) : ‖tau s u i‖ ≤ ‖tau s u j‖ := by sorry
