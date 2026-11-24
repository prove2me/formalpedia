-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unramified_odd_degree_quadratic_local_ext
-- name    : GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:47:40.373696+00:00
-- url     : https://prove2.me/theorems/c3931289-103a-45ab-b292-35ef9414feb7
-- title:
--   T: exists unramified odd degree quadratic local ext
-- statement:
--   The T construction uses the exists unramified odd degree quadratic local ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExtStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExtStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext : ∀ (K : UQ) (d : ℕ), Odd d → ∃ (K' : UQ) (φ : K.E →+* K'.E), K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧ @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d ∧ ∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ := by sorry
