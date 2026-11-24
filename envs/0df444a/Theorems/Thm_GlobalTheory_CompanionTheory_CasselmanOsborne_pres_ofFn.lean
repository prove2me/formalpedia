-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_ofFn
-- name    : GlobalTheory.CompanionTheory.CasselmanOsborne.pres_ofFn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:02.774559+00:00
-- url     : https://prove2.me/theorems/3153af8f-9209-474f-95df-9554a4ba77b8
-- title:
--   Casselman Osborne: pres of Fn
-- statement:
--   The Casselman Osborne construction uses the pres of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L25-L33

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.CasselmanOsborne.pres_ofFn {R : Submodule ℂ (V × W)} : ∀ {t : ℕ} (S : Fin t → Module.End ℂ V)
    (T : Fin t → Module.End ℂ W), (∀ k, Pres R (S k) (T k)) →
    Pres R (List.ofFn S).prod (List.ofFn T).prod
  := by sorry
