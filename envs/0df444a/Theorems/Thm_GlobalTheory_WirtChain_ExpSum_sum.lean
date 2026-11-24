-- Prove2me | Theorems.Thm_GlobalTheory_WirtChain_ExpSum_sum
-- name    : GlobalTheory.WirtChain.ExpSum.sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:00.19581+00:00
-- url     : https://prove2.me/theorems/cb0145fb-c843-4107-9577-44fda9e1c68b
-- title:
--   Exp Sum: sum
-- statement:
--   The Exp Sum construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L78-L85

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

theorem GlobalTheory.WirtChain.ExpSum.sum {α : Type} (s : Finset α) (F : α → ℂ → (I → ℂ) → ℂ) (hF : ∀ a ∈ s, ExpSum U G t l (F a)) :
    ExpSum U G t l fun σ z => ∑ a ∈ s, F a σ z := by sorry
