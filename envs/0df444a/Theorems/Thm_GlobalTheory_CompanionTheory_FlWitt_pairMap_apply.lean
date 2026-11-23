-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pairMap_apply
-- name    : GlobalTheory.CompanionTheory.FlWitt.pairMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:28.898039+00:00
-- url     : https://prove2.me/theorems/6c0ffb94-a53b-4362-ad3b-b076b5a8b05c
-- title:
--   Fl Witt: pair Map apply
-- statement:
--   The Fl Witt construction uses the pair Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L35-L36

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

theorem GlobalTheory.CompanionTheory.FlWitt.pairMap_apply (e f : Fin l → V) (p : (Fin l → L) × (Fin l → L)) :
    pairMap e f p = ∑ i, p.1 i • e i + ∑ i, p.2 i • f i := by sorry
