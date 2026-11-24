-- Prove2me | Theorems.Thm_GlobalTheory_T_adjoin_primitiveRoot_eq_integers_unramifiedQuadratic
-- name    : GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:31:22.991697+00:00
-- url     : https://prove2.me/theorems/2ba08363-afb2-4e56-8360-0474836ddf03
-- title:
--   T: adjoin primitive Root eq integers unramified Quadratic
-- statement:
--   The T construction uses the adjoin primitive Root eq integers unramified Quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by sorry
