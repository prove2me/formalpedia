-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_hasDerivAt_ext
-- name    : GlobalTheory.CompanionTheory.SmBracket.hasDerivAt_ext
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:33.979301+00:00
-- url     : https://prove2.me/theorems/d257cd6a-34fd-49de-b34f-95308c2ea8dd
-- title:
--   Sm Bracket: has Deriv At ext
-- statement:
--   The Sm Bracket construction uses the has Deriv At ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExt.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExt.lean#L47-L52

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

theorem GlobalTheory.CompanionTheory.SmBracket.hasDerivAt_ext (h : RepOn G σ) {X g : Mat n} (hX : ∀ t, ex X t ∈ G) (hg : g ∈ G) {f F : Mat n → H}
    {U : Set (Mat n)} (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ G → f x = F x) :
    HasDerivAt (fun t => f (g * ex X t)) (fderiv ℝ F g (g * X)) 0 := by sorry
