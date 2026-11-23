-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_cext_apply
-- name    : GlobalTheory.CompanionTheory.SmoothModule.cext_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:40.868769+00:00
-- url     : https://prove2.me/theorems/0b584ac8-60e0-4352-91ea-6c3b6245cc73
-- title:
--   Smooth Module: cext apply
-- statement:
--   The Smooth Module construction uses the cext apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L208-L211

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

theorem GlobalTheory.CompanionTheory.SmoothModule.cext_apply {M : Type*} [AddCommGroup M] [Module ℂ M] (d : Matrix (Fin n) (Fin n) ℂ → M)
    (hadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y)
    (hsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cext ε d hadd hsmul Y = d (re ε Y) + Complex.I • d (im ε Y) := by sorry
