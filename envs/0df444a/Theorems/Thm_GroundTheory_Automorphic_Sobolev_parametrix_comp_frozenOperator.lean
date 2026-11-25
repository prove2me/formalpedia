-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_parametrix_comp_frozenOperator
-- name    : GroundTheory.Automorphic.Sobolev.parametrix_comp_frozenOperator
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:51.548805+00:00
-- url     : https://prove2.me/theorems/c1b89a6a-46b2-4376-9697-a70eccae34a2
-- title:
--   Sobolev: parametrix comp frozen Operator
-- statement:
--   The Sobolev construction uses the parametrix comp frozen Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L538-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L538-L544

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (x₀ : E)

theorem GroundTheory.Automorphic.Sobolev.parametrix_comp_frozenOperator {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    Qop a w x₀ μ k ∘L P0 a w x₀ = ContinuousLinearMap.id ℂ 𝓢'(E, ℂ) - Rop a w x₀ μ k := by sorry
