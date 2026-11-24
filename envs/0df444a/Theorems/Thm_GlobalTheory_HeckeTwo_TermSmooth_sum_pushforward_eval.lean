-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_sum_pushforward_eval
-- name    : GlobalTheory.HeckeTwo.TermSmooth.sum_pushforward_eval
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:07:07.240161+00:00
-- url     : https://prove2.me/theorems/625c8807-f4ed-449e-a13b-9050039c5f21
-- title:
--   Term Smooth: sum pushforward eval
-- statement:
--   The Term Smooth construction uses the sum pushforward eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivHeckePhiFourierTransformRepr.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivHeckePhiFourierTransformRepr.lean#L13-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformRepr
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth

theorem GlobalTheory.HeckeTwo.TermSmooth.sum_pushforward_eval (σ : ℂ) (F : ℕ × ℕ × ℕ → ℂ) (g : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (c : ℕ × ℕ × ℕ → Polynomial ℂ) (U S' : Finset (ℕ × ℕ × ℕ)) (hU : ∀ p ∈ U, g p ∈ S') :
    ∑ q ∈ S', (∑ p ∈ U, if g p = q then c p else 0).eval σ * F q = ∑ p ∈ U, (c p).eval σ * F (g p) := by sorry
