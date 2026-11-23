-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pair_e
-- name    : GlobalTheory.CompanionTheory.FlWitt.pair_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:52.90868+00:00
-- url     : https://prove2.me/theorems/afa589cd-085d-4c8b-b05d-36a6f94a34cd
-- title:
--   Fl Witt: pair e
-- statement:
--   The Fl Witt construction uses the pair e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L38-L42

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

theorem GlobalTheory.CompanionTheory.FlWitt.pair_e (hh : IsHerm s h) {e f : Fin l → V} (he : ∀ i j, h (e i) (e j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) (j : Fin l)
    (p : (Fin l → L) × (Fin l → L)) : h (e j) (pairMap e f p) = p.2 j * δ := by sorry
