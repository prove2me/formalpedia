-- Prove2me | Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_upper_sub
-- name    : GlobalTheory.UpperHalfImaginaryForm.upper_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:14:12.357553+00:00
-- url     : https://prove2.me/theorems/b1fcfd1e-ecf7-4869-817f-d035bb3bca0c
-- title:
--   Upper Half Imaginary Form: upper sub
-- statement:
--   The Upper Half Imaginary Form construction uses the upper sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImFormApply.lean#L45-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImFormApply.lean#L45-L60

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
variable {n : ℕ}

theorem GlobalTheory.UpperHalfImaginaryForm.upper_sub (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (x y : EuclideanSpace ℂ ι) :
    imForm x y = upper b x y - upper b y x := by sorry
