-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_lt
-- name    : GlobalTheory.CompanionTheory.DSNormLt.pair_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:29.503857+00:00
-- url     : https://prove2.me/theorems/574b1493-1e20-481d-9432-fdf32f40d696
-- title:
--   DSNorm Lt: pair lt
-- statement:
--   The DSNorm Lt construction uses the pair lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L82-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L82-L95

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

theorem GlobalTheory.CompanionTheory.DSNormLt.pair_lt (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1)
    {lam : Fin n → ℝ} (hl : StrictAnti lam) (c d : Fin n) (hcd : c ≠ d) (hne : t c d = - sig c d) :
    ∑ a, lam a * ((∑ b, t a b) / 2) < ∑ a, lam a * ((∑ b, sig a b) / 2) := by sorry
