-- Prove2me | Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_imForm_apply
-- name    : GlobalTheory.UpperHalfImaginaryForm.imForm_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:19.82896+00:00
-- url     : https://prove2.me/theorems/6ba6d5b5-d5ea-4ddc-b7f1-63da6dc9f864
-- title:
--   Upper Half Imaginary Form: im Form apply
-- statement:
--   The Upper Half Imaginary Form construction uses the im Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImFormApply.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImFormApply.lean#L28-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpperHalfImaginaryForm
open ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.UpperHalfImaginaryForm.imForm_apply (x y : EuclideanSpace ℂ ι) : imForm x y = (Hf x y).im := by sorry
