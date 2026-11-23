-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_eq
-- name    : GlobalTheory.CompanionTheory.DSNormLt.pair_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:54.774085+00:00
-- url     : https://prove2.me/theorems/c7e22107-9be2-4680-90cf-f601f66953a4
-- title:
--   DSNorm Lt: pair eq
-- statement:
--   The DSNorm Lt construction uses the pair eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L31-L44

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

theorem GlobalTheory.CompanionTheory.DSNormLt.pair_eq (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (x : Fin n → ℝ) :
    4 * ∑ a, x a * ((∑ b, t a b) / 2) = ∑ a, ∑ b, t a b * (x a - x b) := by sorry
