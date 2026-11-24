-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_heckeTermDecayFourierIntegral_le
-- name    : GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:39.889521+00:00
-- url     : https://prove2.me/theorems/64fa6945-95cb-469f-b7c0-072eb945831c
-- title:
--   T: norm hecke Term Decay Fourier Integral le
-- statement:
--   The T construction uses the norm hecke Term Decay Fourier Integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormHeckeTermDecayFourierIntegralLeStatement.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormHeckeTermDecayFourierIntegralLeStatement.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeTermDecayFourierIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeTermDecayFourierIntegralLeStatement
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
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) := by sorry
