-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_normSq_le
-- name    : GlobalTheory.CompanionTheory.DSNormLt.normSq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:25.054908+00:00
-- url     : https://prove2.me/theorems/e931f68b-288d-426c-9659-51e6b00cffbc
-- title:
--   DSNorm Lt: norm Sq le
-- statement:
--   The DSNorm Lt construction uses the norm Sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L52-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L52-L80

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSNormLt.normSq_le (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1) :
    ∑ a, ((∑ b, t a b) / 2) ^ 2 ≤ ∑ a : Fin n, ((∑ b, sig a b) / 2) ^ 2 := by sorry
