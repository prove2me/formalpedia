-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_skew
-- name    : GlobalTheory.CompanionTheory.SmoothModule.skew
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:15:10.118079+00:00
-- url     : https://prove2.me/theorems/9f89b732-5497-42d5-8254-73ca05416bd1
-- title:
--   Smooth Module: skew
-- statement:
--   The Smooth Module construction uses the skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L265-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L265-L273

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

theorem GlobalTheory.CompanionTheory.SmoothModule.skew (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v w v' w' : H}
    (hv : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0)
    (hw : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) w) w' 0) :
    ⟪v', w⟫_ℂ = -⟪v, w'⟫_ℂ := by sorry
