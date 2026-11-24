-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pairMap_injective
-- name    : GlobalTheory.CompanionTheory.FlWitt.pairMap_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:17.096213+00:00
-- url     : https://prove2.me/theorems/ff313c70-0ece-4708-8637-e84607745bb5
-- title:
--   Fl Witt: pair Map injective
-- statement:
--   The Fl Witt construction uses the pair Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L66-L79

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

theorem GlobalTheory.CompanionTheory.FlWitt.pairMap_injective (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V}
    (he : ∀ i j, h (e i) (e j) = 0) (hf : ∀ i j, h (f i) (f j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) :
    Function.Injective (pairMap e f : ((Fin l → L) × (Fin l → L)) →ₗ[L] V) := by sorry
