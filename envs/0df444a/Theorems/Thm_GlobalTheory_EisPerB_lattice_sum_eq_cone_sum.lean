-- Prove2me | Theorems.Thm_GlobalTheory_EisPerB_lattice_sum_eq_cone_sum
-- name    : GlobalTheory.EisPerB.lattice_sum_eq_cone_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:38.264579+00:00
-- url     : https://prove2.me/theorems/3da8e843-a3eb-4780-bfc9-404a86e91893
-- title:
--   Eis Per B: lattice sum eq cone sum
-- statement:
--   The Eis Per B construction uses the lattice sum eq cone sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeSumEqConeSum.lean#L60-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeSumEqConeSum.lean#L60-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemTraceDualSignedPositiveConeIffTotallyPositiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisensteinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

theorem GlobalTheory.EisPerB.lattice_sum_eq_cone_sum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
    ∀ (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k → ∀ (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
      Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) ∧
      HasSum (fun a : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F) => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k 0 z ((a : F), b))
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) *
          ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) := by sorry
