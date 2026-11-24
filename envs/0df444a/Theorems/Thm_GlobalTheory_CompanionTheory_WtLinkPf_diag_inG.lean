-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_diag_inG
-- name    : GlobalTheory.CompanionTheory.WtLinkPf.diag_inG
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:36.71187+00:00
-- url     : https://prove2.me/theorems/7e22dcfa-6837-49d0-8084-ff5fe79e3498
-- title:
--   Wt Link Pf: diag in G
-- statement:
--   The Wt Link Pf construction uses the diag in G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HasDerivAtExpMul.lean#L62-L72

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

theorem GlobalTheory.CompanionTheory.WtLinkPf.diag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inG ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by sorry
