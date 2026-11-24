-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKInvLift_exists_adFam
-- name    : GlobalTheory.CompanionTheory.LKInvLift.exists_adFam
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:53.962922+00:00
-- url     : https://prove2.me/theorems/17571470-54bb-4ad3-9266-813ffeb524cc
-- title:
--   LKInv Lift: exists ad Fam
-- statement:
--   The LKInv Lift construction uses the exists ad Fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsAdFam.lean#L23-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsAdFam.lean#L23-L86

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

theorem GlobalTheory.CompanionTheory.LKInvLift.exists_adFam (a : FreeAlgebra ℂ (Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFam w M ∧ a = ∑ i, t i • w i := by sorry
