-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_fTerm_deriv_summable_bound
-- name    : GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:34.92238+00:00
-- url     : https://prove2.me/theorems/26731c3f-f96a-403e-96b9-5fcb9debf1e4
-- title:
--   Hecke Two: f Term deriv summable bound
-- statement:
--   The Hecke Two construction uses the f Term deriv summable bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoTermIteratedFDerivSummableBound.lean#L17-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoTermIteratedFDerivSummableBound.lean#L17-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FTermIteratedFDerivBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinFourierTermMoveUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBalancedUnitMultipleTotallyRealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoTermIteratedFDerivSummableBound
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
open GlobalTheory GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by sorry
