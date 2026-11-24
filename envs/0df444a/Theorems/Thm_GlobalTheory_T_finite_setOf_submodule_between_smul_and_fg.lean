-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_setOf_submodule_between_smul_and_fg
-- name    : GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:45.049832+00:00
-- url     : https://prove2.me/theorems/072178d7-acaa-42bb-b1a4-f1ea16c3bc5b
-- title:
--   T: finite set Of submodule between smul and fg
-- statement:
--   The T construction uses the finite set Of submodule between smul and fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenSmulAndSelfStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenSmulAndSelfStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelfStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by sorry
