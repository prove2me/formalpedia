-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_tor_mem_UJ
-- name    : GlobalTheory.CompanionTheory.WtLinkPf.tor_mem_UJ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:21.945698+00:00
-- url     : https://prove2.me/theorems/6a6b54b3-c804-497d-9692-7d04e052a384
-- title:
--   Wt Link Pf: tor mem UJ
-- statement:
--   The Wt Link Pf construction uses the tor mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L37-L43

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

theorem GlobalTheory.CompanionTheory.WtLinkPf.tor_mem_UJ (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ UJset ε := by sorry
