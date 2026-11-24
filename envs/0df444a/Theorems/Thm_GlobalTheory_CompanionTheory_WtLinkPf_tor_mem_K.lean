-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_tor_mem_K
-- name    : GlobalTheory.CompanionTheory.WtLinkPf.tor_mem_K
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:29.542244+00:00
-- url     : https://prove2.me/theorems/cdb58a7d-c9b8-47ea-ba88-b75b6849338e
-- title:
--   Wt Link Pf: tor mem K
-- statement:
--   The Wt Link Pf construction uses the tor mem K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L45-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L45-L60

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.WtLinkPf.tor_mem_K (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ Kset ε := by sorry
