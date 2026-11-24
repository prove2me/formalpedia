-- Prove2me | Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_isIrreducible_generalizations
-- name    : GlobalTheory.IrreducibleGeneralizations.isIrreducible_generalizations
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:42.137361+00:00
-- url     : https://prove2.me/theorems/b23968a1-5c35-4435-9323-849f1f0628db
-- title:
--   Irreducible Generalizations: is Irreducible generalizations
-- statement:
--   The Irreducible Generalizations construction uses the is Irreducible generalizations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIrreducibleGeneralizations.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIrreducibleGeneralizations.lean#L9-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IrreducibleGeneralizations
open AlgebraicGeometry Topology

theorem GlobalTheory.IrreducibleGeneralizations.isIrreducible_generalizations {X : Scheme.{u_1}} (x : X) [IsDomain (X.presheaf.stalk x)] :
    IsIrreducible {y : X | y ⤳ x} := by sorry
