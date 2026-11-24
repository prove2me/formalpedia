-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_deg_Fop
-- name    : GlobalTheory.CompanionTheory.CasselmanOsborne.deg_Fop
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:31:28.230505+00:00
-- url     : https://prove2.me/theorems/3ab69175-86f0-4de4-a0f9-e3c5fb2e64df
-- title:
--   Casselman Osborne: deg Fop
-- statement:
--   The Casselman Osborne construction uses the deg Fop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L137-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L137-L145

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
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.CasselmanOsborne.deg_Fop (hG : GFacts) {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) {x : Ch ε V}
    (hx : Deg j x) : Deg j (Fop ε E c d x) := by sorry
