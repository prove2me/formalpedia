-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_mul
-- name    : GlobalTheory.CompanionTheory.DSNormLt.sig_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:33.379797+00:00
-- url     : https://prove2.me/theorems/c2b91cc3-526e-4d0a-bac7-026321efc030
-- title:
--   DSNorm Lt: sig mul
-- statement:
--   The DSNorm Lt construction uses the sig mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L24-L29

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

theorem GlobalTheory.CompanionTheory.DSNormLt.sig_mul {y : Fin n → ℝ} (hy : Antitone y) (a b : Fin n) : sig a b * (y a - y b) = |y a - y b| := by sorry
