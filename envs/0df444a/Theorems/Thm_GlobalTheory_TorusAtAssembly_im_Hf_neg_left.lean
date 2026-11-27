-- Prove2me | Theorems.Thm_GlobalTheory_TorusAtAssembly_im_Hf_neg_left
-- name    : GlobalTheory.TorusAtAssembly.im_Hf_neg_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:23.465794+00:00
-- url     : https://prove2.me/theorems/cb0fef8d-d530-46e8-a141-4ac18dcf1343
-- title:
--   Torus At Assembly: im Hf neg left
-- statement:
--   The Torus At Assembly construction uses the im Hf neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TorusAtExistsOfParts.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TorusAtExistsOfParts.lean#L26-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.TorusAtAssembly
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.TorusAtAssembly.im_Hf_neg_left (x z : EuclideanSpace ℂ ι) :
    (Hf (-x) z).im = -(Hf x z).im := by sorry
