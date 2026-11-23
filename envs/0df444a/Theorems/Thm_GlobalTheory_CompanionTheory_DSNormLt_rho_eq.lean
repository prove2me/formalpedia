-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_rho_eq
-- name    : GlobalTheory.CompanionTheory.DSNormLt.rho_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:26.611831+00:00
-- url     : https://prove2.me/theorems/7e1691d8-8bc6-4f16-88ca-66dea3d04a6c
-- title:
--   DSNorm Lt: rho eq
-- statement:
--   The DSNorm Lt construction uses the rho eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L190-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L190-L201

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSNormLt.rho_eq (ε : Fin n → Bool) (a : Fin n) :
    PI.UpqRep.rhoC ε a + PI.UpqRep.rhoN ε a = (∑ b, sig a b) / 2 := by sorry
