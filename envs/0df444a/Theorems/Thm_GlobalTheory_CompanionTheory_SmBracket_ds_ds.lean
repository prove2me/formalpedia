-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_ds_ds
-- name    : GlobalTheory.CompanionTheory.SmBracket.ds_ds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:39.569821+00:00
-- url     : https://prove2.me/theorems/b3845c4f-8508-4f5c-8ad4-359d8a3b79a2
-- title:
--   Sm Bracket: ds ds
-- statement:
--   The Sm Bracket construction uses the ds ds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExt.lean#L54-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExt.lean#L54-L67

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmBracket
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem GlobalTheory.CompanionTheory.SmBracket.ds_ds (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G) {v : H}
    (hv : IsSm G σ v) {F : Mat n → H} {U : Set (Mat n)} (hU : IsOpen U) (h1 : (1 : Mat n) ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ x ∈ U, x ∈ G → σ x v = F x) (L : Mat n →L[ℝ] Mat n)
    (hL : ∀ x, L x = x * Y) :
    ds σ X (ds σ Y v) = fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by sorry
