-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoSum_pow_mul_exp_neg_le
-- name    : GlobalTheory.HeckeTwoSum.pow_mul_exp_neg_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:15:32.105869+00:00
-- url     : https://prove2.me/theorems/f8761e18-149c-4ade-9869-b8ac203725e0
-- title:
--   Hecke Two Sum: pow mul exp neg le
-- statement:
--   The Hecke Two Sum construction uses the pow mul exp neg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHilbertEisensteinWeightTwoQSeries.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHilbertEisensteinWeightTwoQSeries.lean#L18-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwoSum.pow_mul_exp_neg_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (n : ℕ) :
    t ^ n * Real.exp (-(c * t)) ≤ n.factorial / c ^ n := by sorry
