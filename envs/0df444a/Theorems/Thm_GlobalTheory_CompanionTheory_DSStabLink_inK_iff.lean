-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_inK_iff
-- name    : GlobalTheory.CompanionTheory.DSStabLink.inK_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:39.994177+00:00
-- url     : https://prove2.me/theorems/c93ccb0f-048e-42d9-b629-3a551819ec07
-- title:
--   DSStab Link: in K iff
-- statement:
--   The DSStab Link construction uses the in K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExpMemUJ.lean#L89-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExpMemUJ.lean#L89-L116

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSStabLink.inK_iff (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ (∀ c d, ε c ≠ ε d → X c d = 0) ∧ ∀ c d, star (X d c) = -X c d := by sorry
