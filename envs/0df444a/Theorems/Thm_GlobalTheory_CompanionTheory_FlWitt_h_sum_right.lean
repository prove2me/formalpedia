-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_h_sum_right
-- name    : GlobalTheory.CompanionTheory.FlWitt.h_sum_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:55:06.717224+00:00
-- url     : https://prove2.me/theorems/fbc6626b-1206-47a8-ac08-f7ea203f325b
-- title:
--   Fl Witt: h sum right
-- statement:
--   The Fl Witt construction uses the h sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L20-L25

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

theorem GlobalTheory.CompanionTheory.FlWitt.h_sum_right (hh : IsHerm s h) {ι : Type} (t : Finset ι) (x : V) (c : ι → L) (v : ι → V) :
    h x (∑ i ∈ t, c i • v i) = ∑ i ∈ t, c i * h x (v i) := by sorry
