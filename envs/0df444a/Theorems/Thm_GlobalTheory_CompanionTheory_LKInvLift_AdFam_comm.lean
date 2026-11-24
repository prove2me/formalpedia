-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKInvLift_AdFam_comm
-- name    : GlobalTheory.CompanionTheory.LKInvLift.AdFam.comm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:20.632052+00:00
-- url     : https://prove2.me/theorems/a673567a-5b6e-4d2c-b90e-b15680c62c8f
-- title:
--   Ad Fam: comm
-- statement:
--   The Ad Fam construction uses the comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsAdFam.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsAdFam.lean#L88-L96

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsAdFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKInvLift
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC (KStab)
open CompanionTheory.D.LK
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.LKInvLift.AdFam.comm {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFam w M) {V : Type} [AddCommGroup V] [Module ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c d : Fin n) (t : ι → ℂ) :
    E c d * ev E (∑ i, t i • w i) - ev E (∑ i, t i • w i) * E c d = ev E (∑ j, (M c d *ᵥ t) j • w j) := by sorry
