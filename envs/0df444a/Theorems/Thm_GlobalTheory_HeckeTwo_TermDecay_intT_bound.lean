-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_intT_bound
-- name    : GlobalTheory.HeckeTwo.TermDecay.intT_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:30.962226+00:00
-- url     : https://prove2.me/theorems/b58c3de8-0a34-4c09-b46e-33423e19a689
-- title:
--   Term Decay: int T bound
-- statement:
--   The Term Decay construction uses the int T bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeYDerivativeTermIntegralPolynomialDecay.lean#L169-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeYDerivativeTermIntegralPolynomialDecay.lean#L169-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeTermDecayFourierIntegralLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtHeckeTermDecayIntegrandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermIntegralPolynomialDecay
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
open GlobalTheory.HeckeTwo.TermDecay

theorem GlobalTheory.HeckeTwo.TermDecay.intT_bound : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by sorry
