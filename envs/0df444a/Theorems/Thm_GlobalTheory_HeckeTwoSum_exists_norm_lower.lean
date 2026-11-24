-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoSum_exists_norm_lower
-- name    : GlobalTheory.HeckeTwoSum.exists_norm_lower
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:15:21.459373+00:00
-- url     : https://prove2.me/theorems/e33ccf89-75ee-4f7a-acd2-158836f89279
-- title:
--   Hecke Two Sum: exists norm lower
-- statement:
--   The Hecke Two Sum construction uses the exists norm lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHilbertEisensteinWeightTwoQSeries.lean#L29-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHilbertEisensteinWeightTwoQSeries.lean#L29-L52

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

theorem GlobalTheory.HeckeTwoSum.exists_norm_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ν ∈ I, ν ≠ 0 → κ ≤ |((Algebra.norm ℚ ν : ℚ) : ℝ)| := by sorry
