-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_UJ_inv
-- name    : GlobalTheory.CompanionTheory.SmoothModule.UJ_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:47.209191+00:00
-- url     : https://prove2.me/theorems/55ded045-3560-41de-a177-b858b256f0a0
-- title:
--   Smooth Module: UJ inv
-- statement:
--   The Smooth Module construction uses the UJ inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L125-L126

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
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
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.SmoothModule.UJ_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : g⁻¹ = Jm ε * gᴴ * Jm ε := by sorry
