-- Prove2me | Theorems.Thm_GlobalTheory_WirtChain_differentiableOn_wirtWord_mul_exp_comp
-- name    : GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:56:41.856192+00:00
-- url     : https://prove2.me/theorems/f160e318-8dcc-4c58-bbc2-e0cb4ee7d6bc
-- title:
--   Wirt Chain: differentiable On wirt Word mul exp comp
-- statement:
--   The Wirt Chain construction uses the differentiable On wirt Word mul exp comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L184-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L184-L206

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
open Classical

theorem GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by sorry
