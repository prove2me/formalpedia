-- Prove2me | Theorems.Thm_GlobalTheory_T_isReduced_of_separable_markedCharpoly
-- name    : GlobalTheory.T.isReduced_of_separable_markedCharpoly
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:49:54.187064+00:00
-- url     : https://prove2.me/theorems/3cc6575b-bf4a-4513-9881-4e2c67630f5d
-- title:
--   T: is Reduced of separable marked Charpoly
-- statement:
--   The T construction uses the is Reduced of separable marked Charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsReducedOfSeparableMarkedCharpolyStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsReducedOfSeparableMarkedCharpolyStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpolyStatement
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

theorem GlobalTheory.T.isReduced_of_separable_markedCharpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by sorry
