-- Prove2me | Theorems.Thm_GlobalTheory_WirtChain_ExpSum_const_mul
-- name    : GlobalTheory.WirtChain.ExpSum.const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:46.360597+00:00
-- url     : https://prove2.me/theorems/ad072e4d-4e30-4567-8c17-cdf6feedc7bc
-- title:
--   Exp Sum: const mul
-- statement:
--   The Exp Sum construction uses the const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L65-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L65-L76

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
variable (U : Set (I → ℂ)) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (l : (I → ℂ) → ℂ)
variable {U G t l}

theorem GlobalTheory.WirtChain.ExpSum.const_mul {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (c : ℂ) :
    ExpSum U G t l fun σ z => c * F σ z := by sorry
