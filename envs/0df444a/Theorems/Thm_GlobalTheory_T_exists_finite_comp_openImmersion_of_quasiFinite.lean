-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_comp_openImmersion_of_quasiFinite
-- name    : GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:23.948871+00:00
-- url     : https://prove2.me/theorems/9a4190ce-2c42-4226-b57c-af7ef33fa5da
-- title:
--   T: exists finite comp open Immersion of quasi Finite
-- statement:
--   The T construction uses the exists finite comp open Immersion of quasi Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFiniteStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFiniteStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f → ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by sorry
