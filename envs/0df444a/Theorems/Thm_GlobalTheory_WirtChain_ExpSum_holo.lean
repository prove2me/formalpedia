-- Prove2me | Theorems.Thm_GlobalTheory_WirtChain_ExpSum_holo
-- name    : GlobalTheory.WirtChain.ExpSum.holo
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:56:36.435314+00:00
-- url     : https://prove2.me/theorems/d9b4370d-bc9b-47a4-8aec-744261a66ae1
-- title:
--   Exp Sum: holo
-- statement:
--   The Exp Sum construction uses the holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L87-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L87-L96

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

theorem GlobalTheory.WirtChain.ExpSum.holo {D : Set ℂ} {V : Set (Φ → ℂ)} (hmaps : Set.MapsTo t U V)
    (hGh : ∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {z : I → ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (fun σ => F σ z) D := by sorry
