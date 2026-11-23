-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_blk_val
-- name    : GlobalTheory.CompanionTheory.CapelliBlocks.blk_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:20.499417+00:00
-- url     : https://prove2.me/theorems/50e2fbca-beed-47c6-8c58-19c24bcdcdbe
-- title:
--   Capelli Blocks: blk val
-- statement:
--   The Capelli Blocks construction uses the blk val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean#L156-L158

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CapelliBlocks.blk_val (ε : Fin n → Bool) (s : Bool) (k : Fin (nb ε s)) : ε (blk ε s k) = s := by sorry
