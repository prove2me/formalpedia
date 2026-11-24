-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermBoundDeriv_iteratedDeriv_hTrans_bound
-- name    : GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:07:22.56307+00:00
-- url     : https://prove2.me/theorems/956a735f-499d-4287-a936-5ab772089f9e
-- title:
--   Term Bound Deriv: iterated Deriv h Trans bound
-- statement:
--   The Term Bound Deriv construction uses the iterated Deriv h Trans bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivHeckePhiFourierTransformBound.lean#L35-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivHeckePhiFourierTransformBound.lean#L35-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformBound
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermBoundDeriv

theorem GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound :
    (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by sorry
