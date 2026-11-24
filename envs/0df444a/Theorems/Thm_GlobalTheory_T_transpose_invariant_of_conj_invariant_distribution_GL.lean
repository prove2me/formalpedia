-- Prove2me | Theorems.Thm_GlobalTheory_T_transpose_invariant_of_conj_invariant_distribution_GL
-- name    : GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:00:46.495277+00:00
-- url     : https://prove2.me/theorems/ee5eb80b-6cd8-4ab3-8435-d3ae2c5b9a46
-- title:
--   T: transpose invariant of conj invariant distribution GL
-- statement:
--   The T construction uses the transpose invariant of conj invariant distribution GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransposeInvariantOfConjInvariantDistributionGLStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransposeInvariantOfConjInvariantDistributionGLStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGLStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ), (∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) → ∀ φ ψ : SB (GL n k), (∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) → T ψ = T φ := by sorry
