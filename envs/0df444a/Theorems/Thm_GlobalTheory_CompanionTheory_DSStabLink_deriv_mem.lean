-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_deriv_mem
-- name    : GlobalTheory.CompanionTheory.DSStabLink.deriv_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:25.512251+00:00
-- url     : https://prove2.me/theorems/c3783f90-4155-4a2d-bd3b-62d57ec23620
-- title:
--   DSStab Link: deriv mem
-- statement:
--   The DSStab Link construction uses the deriv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExpMemUJ.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExpMemUJ.lean#L72-L85

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC

theorem GlobalTheory.CompanionTheory.DSStabLink.deriv_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (c : ℝ → H) (z : H) (hc : ∀ t, c t ∈ W) (hz : HasDerivAt c z 0) :
    z ∈ W := by sorry
