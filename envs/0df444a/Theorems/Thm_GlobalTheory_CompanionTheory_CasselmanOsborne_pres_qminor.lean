-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_qminor
-- name    : GlobalTheory.CompanionTheory.CasselmanOsborne.pres_qminor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:09.798516+00:00
-- url     : https://prove2.me/theorems/f4d6d7e5-0c99-4f8f-aba3-2035c8151826
-- title:
--   Casselman Osborne: pres qminor
-- statement:
--   The Casselman Osborne construction uses the pres qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L35-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L35-L61

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

theorem GlobalTheory.CompanionTheory.CasselmanOsborne.pres_qminor {n t : ℕ} {R : Submodule ℂ (V × W)} (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (a b : Fin t → Fin n)
    (h : ∀ i j, Pres R (E (a i) (b j)) (F (a i) (b j))) (u : ℂ) :
    Pres R (qminor E a b u) (qminor F a b u) := by sorry
