-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_LatSum_exists_absSum_lower
-- name    : GlobalTheory.HeckeTwo.LatSum.exists_absSum_lower
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:05:48.430127+00:00
-- url     : https://prove2.me/theorems/9a499944-6e6b-4e6c-9b11-61422be6efd6
-- title:
--   Lat Sum: exists abs Sum lower
-- statement:
--   The Lat Sum construction uses the exists abs Sum lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeBalancedLatticeDoubleSum.lean#L80-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeBalancedLatticeDoubleSum.lean#L80-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.LatSum
variable {F : Type} [Field F] [NumberField F]
variable [IsTotallyReal F]

theorem GlobalTheory.HeckeTwo.LatSum.exists_absSum_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ I, x ≠ 0 → β ≤ absSum x := by sorry
