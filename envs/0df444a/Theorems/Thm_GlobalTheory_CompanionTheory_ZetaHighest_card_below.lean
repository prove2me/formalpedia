-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_card_below
-- name    : GlobalTheory.CompanionTheory.ZetaHighest.card_below
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:51.169806+00:00
-- url     : https://prove2.me/theorems/83866ecf-373d-4b06-bb02-d57b8529d186
-- title:
--   Zeta Highest: card below
-- statement:
--   The Zeta Highest construction uses the card below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L38-L52

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

theorem GlobalTheory.CompanionTheory.ZetaHighest.card_below (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) :
    (univ.filter fun b => b < blk ε s i ∧ ε b = ε (blk ε s i)).card = i := by sorry
