-- Prove2me | Theorems.Thm_GlobalTheory_BalancedUnits_sum_mult_log_sub
-- name    : GlobalTheory.BalancedUnits.sum_mult_log_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:20.715712+00:00
-- url     : https://prove2.me/theorems/875cc30f-9fb8-4f15-b591-76a6b5c19f44
-- title:
--   Balanced Units: sum mult log sub
-- statement:
--   The Balanced Units construction uses the sum mult log sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBalancedUnitMultipleTotallyReal.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBalancedUnitMultipleTotallyReal.lean#L16-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBalancedUnitMultipleTotallyReal
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
open GlobalTheory GlobalTheory.BalancedUnits
open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem

theorem GlobalTheory.BalancedUnits.sum_mult_log_sub {K : Type} [Field K] [NumberField K] (x : mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) = 0 := by sorry
