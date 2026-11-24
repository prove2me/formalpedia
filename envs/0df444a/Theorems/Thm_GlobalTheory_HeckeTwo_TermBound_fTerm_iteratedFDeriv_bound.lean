-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermBound_fTerm_iteratedFDeriv_bound
-- name    : GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:07:43.439859+00:00
-- url     : https://prove2.me/theorems/f20a1535-d6dd-4e7a-bc48-019cf132b645
-- title:
--   Term Bound: f Term iterated FDeriv bound
-- statement:
--   The Term Bound construction uses the f Term iterated FDeriv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FTermIteratedFDerivBound.lean#L33-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FTermIteratedFDerivBound.lean#L33-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPiUpperHalfPlaneImBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivProdCoordLeLeibnizStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformReprStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermIntegralPolynomialDecayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivHeckeFourierFactorLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FTermIteratedFDerivBound
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermBound

theorem GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by sorry
