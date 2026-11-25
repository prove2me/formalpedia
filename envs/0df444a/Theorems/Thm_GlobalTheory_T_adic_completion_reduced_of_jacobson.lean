-- Prove2me | Theorems.Thm_GlobalTheory_T_adic_completion_reduced_of_jacobson
-- name    : GlobalTheory.T.adic_completion_reduced_of_jacobson
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:30.503016+00:00
-- url     : https://prove2.me/theorems/eee7c603-7bad-58da-b03c-a31356e7113a
-- title:
--   T: adic completion reduced of jacobson
-- statement:
--   The T construction uses the adic completion reduced of jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionReducedOfJacobsonStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionReducedOfJacobsonStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobson
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobsonStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adic_completion_reduced_of_jacobson : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D] (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by sorry
