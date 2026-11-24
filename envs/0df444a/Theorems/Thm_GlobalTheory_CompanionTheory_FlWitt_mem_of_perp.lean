-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_mem_of_perp
-- name    : GlobalTheory.CompanionTheory.FlWitt.mem_of_perp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:41:45.815342+00:00
-- url     : https://prove2.me/theorems/134bcdff-7223-4880-9e3b-59f4c5a4d1a1
-- title:
--   Fl Witt: mem of perp
-- statement:
--   The Fl Witt construction uses the mem of perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L81-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L81-L99

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

theorem GlobalTheory.CompanionTheory.FlWitt.mem_of_perp (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V} {W : Submodule L V}
    (F : IsFrame h δ e f W) (x : V) (h1 : ∀ i, h (e i) x = 0) (h2 : ∀ i, h (f i) x = 0) : x ∈ W := by sorry
