-- Prove2me | Theorems.Thm_GlobalTheory_T_unramifiedQuadratic_exists_integers_uniformiser
-- name    : GlobalTheory.T.unramifiedQuadratic_exists_integers_uniformiser
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:51.380647+00:00
-- url     : https://prove2.me/theorems/0b74db96-0756-4e04-a1bd-3e2598b93c54
-- title:
--   T: unramified Quadratic exists integers uniformiser
-- statement:
--   The T construction uses the unramified Quadratic exists integers uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticExistsIntegersUniformiserStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticExistsIntegersUniformiserStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticExistsIntegersUniformiser
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticExistsIntegersUniformiserStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unramifiedQuadratic_exists_integers_uniformiser : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∃ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) ∧ IsCompact (O : Set A.L) ∧ (∀ y ∈ O, star y ∈ O) ∧ (¬ ∃ y, A.NL y = (ϖ : A.K)) ∧ algebraMap A.K A.L (ϖ : A.K) ∈ O ∧ (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) ∧ (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) ∧ (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) ∧ ∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O := by sorry
