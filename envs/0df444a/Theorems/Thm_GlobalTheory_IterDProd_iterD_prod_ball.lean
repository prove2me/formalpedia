-- Prove2me | Theorems.Thm_GlobalTheory_IterDProd_iterD_prod_ball
-- name    : GlobalTheory.IterDProd.iterD_prod_ball
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:22:40.352868+00:00
-- url     : https://prove2.me/theorems/15396d87-abe4-4d11-8701-205ab3a38f5b
-- title:
--   Iter DProd: iter D prod ball
-- statement:
--   The Iter DProd construction uses the iter D prod ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedPartialDerivProdOneVarAtZero.lean#L37-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedPartialDerivProdOneVarAtZero.lean#L37-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivProdOneVarAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.IterDProd

theorem GlobalTheory.IterDProd.iterD_prod_ball {I : Type} [Fintype I] [DecidableEq I] (u : List I) (r : ℝ)
    (ψ : I → ℂ → ℂ) (A : ℂ) (hr : 0 < r) (hψ : ∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) :
    ∀ z ∈ Metric.ball (0 : I → ℂ) r, iterD u (fun z ↦ A * ∏ i, ψ i (z i)) z
      = A * ∏ i, iteratedDeriv (u.count i) (ψ i) (z i) := by sorry
