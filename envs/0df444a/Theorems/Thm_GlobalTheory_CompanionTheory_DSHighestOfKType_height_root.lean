-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSHighestOfKType_height_root
-- name    : GlobalTheory.CompanionTheory.DSHighestOfKType.height_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:06.562375+00:00
-- url     : https://prove2.me/theorems/dcd737aa-4496-40b6-b91b-43d25f294a1a
-- title:
--   DSHighest Of KType: height root
-- statement:
--   The DSHighest Of KType construction uses the height root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L14-L15

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NotCdomAddRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSHighestOfKType
open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSHighestOfKType.height_root (a b : Fin n) : ∑ i : Fin n, ((i : ℕ) : ℝ) * root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by sorry
