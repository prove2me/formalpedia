-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_prod_blk
-- name    : GlobalTheory.CompanionTheory.ZetaHighest.prod_blk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:55.664575+00:00
-- url     : https://prove2.me/theorems/eb01bb22-d039-49cc-8f13-dfcc3f526603
-- title:
--   Zeta Highest: prod blk
-- statement:
--   The Zeta Highest construction uses the prod blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L28-L36

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

theorem GlobalTheory.CompanionTheory.ZetaHighest.prod_blk (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℂ) :
    ∏ i, f (blk ε s i) = ∏ a ∈ univ.filter (fun a => ε a = s), f a := by sorry
