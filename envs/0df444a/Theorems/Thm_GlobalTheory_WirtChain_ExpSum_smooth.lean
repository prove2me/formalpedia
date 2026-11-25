-- Prove2me | Theorems.Thm_GlobalTheory_WirtChain_ExpSum_smooth
-- name    : GlobalTheory.WirtChain.ExpSum.smooth
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:06.556574+00:00
-- url     : https://prove2.me/theorems/0b8485e8-fc6d-4849-8da7-6a00a18c1c28
-- title:
--   Exp Sum: smooth
-- statement:
--   The Exp Sum construction uses the smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L98-L108

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

theorem GlobalTheory.WirtChain.ExpSum.smooth {D : Set ℂ} {V : Set (Φ → ℂ)} (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {σ : ℂ} (hσ : σ ∈ D) :
    ContDiffOn ℝ ∞ (F σ) U := by sorry
