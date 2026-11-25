-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_frame_core
-- name    : GlobalTheory.CompanionTheory.FlWitt.frame_core
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:21.937828+00:00
-- url     : https://prove2.me/theorems/0ace68b8-e555-4b2a-912f-67ef8cc7dd6f
-- title:
--   Fl Witt: frame core
-- statement:
--   The Fl Witt construction uses the frame core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L161-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L161-L207

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlWitt
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}

theorem GlobalTheory.CompanionTheory.FlWitt.frame_core [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (hd : δ ≠ 0) {l' : ℕ} (hl : l ≤ l') {e f : Fin l → V} {W : Submodule L V}
    {e' f' : Fin l' → V} {W' : Submodule L V}
    (F : IsFrame h δ e f W) (F' : IsFrame h δ e' f' W') :
    ∃ (q : Fin l ≃ Fin l') (g : V ≃ₗ[L] V), IsIso h g ∧ (∀ i, g (e i) = e' (q i)) ∧
      (∀ i, g (f i) = f' (q i)) ∧ ∀ w, w ∈ W ↔ g w ∈ W' := by sorry
