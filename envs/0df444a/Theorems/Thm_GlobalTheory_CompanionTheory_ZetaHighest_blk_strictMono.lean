-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_strictMono
-- name    : GlobalTheory.CompanionTheory.ZetaHighest.blk_strictMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:21.519803+00:00
-- url     : https://prove2.me/theorems/fb1d4a5b-8e1e-440e-ac24-548fe449959e
-- title:
--   Zeta Highest: blk strict Mono
-- statement:
--   The Zeta Highest construction uses the blk strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkStrictMono.lean#L15-L16

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

theorem GlobalTheory.CompanionTheory.ZetaHighest.blk_strictMono (ε : Fin n → Bool) (s : Bool) : StrictMono (blk ε s) := by sorry
