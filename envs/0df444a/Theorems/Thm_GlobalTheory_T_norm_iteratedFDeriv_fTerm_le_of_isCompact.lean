-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_iteratedFDeriv_fTerm_le_of_isCompact
-- name    : GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:40.974845+00:00
-- url     : https://prove2.me/theorems/a369364c-9962-48c2-b706-6198138d1456
-- title:
--   T: norm iterated FDeriv f Term le of is Compact
-- statement:
--   The T construction uses the norm iterated FDeriv f Term le of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FTermIteratedFDerivBoundStatement.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FTermIteratedFDerivBoundStatement.lean#L11-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FTermIteratedFDerivBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FTermIteratedFDerivBoundStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by sorry
