-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_card_total
-- name    : GlobalTheory.CompanionTheory.ZetaHighest.card_total
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:44.844731+00:00
-- url     : https://prove2.me/theorems/da635096-26c2-4e10-bfce-01cc0dbe8395
-- title:
--   Zeta Highest: card total
-- statement:
--   The Zeta Highest construction uses the card total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L54-L68

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

theorem GlobalTheory.CompanionTheory.ZetaHighest.card_total (ε : Fin n → Bool) (c : Fin n) :
    ((univ.filter fun b => c < b ∧ ε b = ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b = ε c).card : ℝ) +
      ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) + 1
      = n := by sorry
