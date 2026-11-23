-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_graph
-- name    : GlobalTheory.CompanionTheory.CasselmanOsborne.pres_graph
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:11.707789+00:00
-- url     : https://prove2.me/theorems/58a3e552-f109-4062-aefe-20e9697e1d25
-- title:
--   Casselman Osborne: pres graph
-- statement:
--   The Casselman Osborne construction uses the pres graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L74-L82

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

theorem GlobalTheory.CompanionTheory.CasselmanOsborne.pres_graph (φ : V →ₗ[ℂ] W) (S : Module.End ℂ V) (T : Module.End ℂ W) :
    Pres φ.graph S T ↔ ∀ x, φ (S x) = T (φ x) := by sorry
