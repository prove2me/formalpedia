-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_conj_deriv
-- name    : GlobalTheory.CompanionTheory.SmoothModule.conj_deriv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:48.43764+00:00
-- url     : https://prove2.me/theorems/4c486521-c314-4cc1-a0b3-fba16fdf309d
-- title:
--   Smooth Module: conj deriv
-- statement:
--   The Smooth Module construction uses the conj deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L275-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L275-L289

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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem GlobalTheory.CompanionTheory.SmoothModule.conj_deriv (hσ : IsURepOn (UJset ε) σ) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hg : g ∈ UJset ε) {v v' : H}
    (hv : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g v)) (σ g v') 0 := by sorry
