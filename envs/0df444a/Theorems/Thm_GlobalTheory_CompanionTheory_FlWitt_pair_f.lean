-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pair_f
-- name    : GlobalTheory.CompanionTheory.FlWitt.pair_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:55:43.560421+00:00
-- url     : https://prove2.me/theorems/33330f94-c996-4547-bb1a-18793796208e
-- title:
--   Fl Witt: pair f
-- statement:
--   The Fl Witt construction uses the pair f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L44-L52

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

theorem GlobalTheory.CompanionTheory.FlWitt.pair_f (hh : IsHerm s h) {e f : Fin l → V} (hf : ∀ i j, h (f i) (f j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) (j : Fin l)
    (p : (Fin l → L) × (Fin l → L)) : h (f j) (pairMap e f p) = p.1 j * s δ := by sorry
