-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_pd_comm
-- name    : GlobalTheory.CompanionTheory.DSCover.pd_comm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:38.742978+00:00
-- url     : https://prove2.me/theorems/560e2361-4b7f-440d-b301-782f0dd188de
-- title:
--   DSCover: pd comm
-- statement:
--   The DSCover construction uses the pd comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordMonomial.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordMonomial.lean#L46-L56

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
variable {σ : Type}

theorem GlobalTheory.CompanionTheory.DSCover.pd_comm (i j : σ) : pd i * pd j = pd j * pd i := by sorry
