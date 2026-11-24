-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_gam_false
-- name    : GlobalTheory.CompanionTheory.ZetaHighest.gam_false
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:07.388544+00:00
-- url     : https://prove2.me/theorems/7269d262-9f9e-4bef-96df-d99d2648228a
-- title:
--   Zeta Highest: gam false
-- statement:
--   The Zeta Highest construction uses the gam false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L132-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L132-L140

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.ZetaHighest.gam_false (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε false)) :
    gam ε lam (blk ε false i) = lam (blk ε false i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by sorry
