-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_aeval_eq_of_mulLeft_charpoly_separable
-- name    : GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:34:43.165571+00:00
-- url     : https://prove2.me/theorems/89f5bc9c-fd37-485c-b66b-9a7e7149bf29
-- title:
--   T: exists aeval eq of mul Left charpoly separable
-- statement:
--   The T construction uses the exists aeval eq of mul Left charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfMulLeftCharpolySeparableStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfMulLeftCharpolySeparableStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparableStatement
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

theorem GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by sorry
