-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_end_ext
-- name    : GlobalTheory.CompanionTheory.Iwahori.end_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:33.506703+00:00
-- url     : https://prove2.me/theorems/fd5a2d22-873e-4e3e-a76b-36c39ae16328
-- title:
--   Iwahori: end ext
-- statement:
--   The Iwahori construction uses the end ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsPiecesPiece.lean#L101-L105

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

theorem GlobalTheory.CompanionTheory.Iwahori.end_ext (hF : IsFrame h δ e f W) {A B : Module.End L V} (he : ∀ i, A (e i) = B (e i))
    (hf : ∀ i, A (f i) = B (f i)) (hw : ∀ w ∈ W, A w = B w) : A = B := by sorry
