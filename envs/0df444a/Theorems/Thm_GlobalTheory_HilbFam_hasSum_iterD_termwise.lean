-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_hasSum_iterD_termwise
-- name    : GlobalTheory.HilbFam.hasSum_iterD_termwise
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:20:40.937995+00:00
-- url     : https://prove2.me/theorems/8a4b2b56-baea-45f6-842a-1c48c592d08a
-- title:
--   Hilb Fam: has Sum iter D termwise
-- statement:
--   The Hilb Fam construction uses the has Sum iter D termwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumIteratedComplexPartialDerivTermwise.lean#L56-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumIteratedComplexPartialDerivTermwise.lean#L56-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedComplexPartialDerivTermwise
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
open GlobalTheory GlobalTheory.HilbFam
open Set Filter Topology
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors

theorem GlobalTheory.HilbFam.hasSum_iterD_termwise : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ)
    (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M →
    (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) →
    (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) →
    (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) →
    HasSum (fun ξ ↦ _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (f ξ) 0) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) := by sorry
