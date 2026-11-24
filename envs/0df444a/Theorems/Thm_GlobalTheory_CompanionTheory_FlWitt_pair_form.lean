-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pair_form
-- name    : GlobalTheory.CompanionTheory.FlWitt.pair_form
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:38.010796+00:00
-- url     : https://prove2.me/theorems/b25eb214-421d-48b5-9906-28e271825f3f
-- title:
--   Fl Witt: pair form
-- statement:
--   The Fl Witt construction uses the pair form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L54-L64

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

theorem GlobalTheory.CompanionTheory.FlWitt.pair_form (hh : IsHerm s h) {e f : Fin l → V} (he : ∀ i j, h (e i) (e j) = 0)
    (hf : ∀ i j, h (f i) (f j) = 0) (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0)
    (p r : (Fin l → L) × (Fin l → L)) :
    h (pairMap e f p) (pairMap e f r) =
      ∑ j, r.1 j * s (p.2 j * δ) + ∑ j, r.2 j * s (p.1 j * s δ) := by sorry
