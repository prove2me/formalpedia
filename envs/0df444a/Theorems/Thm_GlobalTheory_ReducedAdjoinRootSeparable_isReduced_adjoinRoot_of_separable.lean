-- Prove2me | Theorems.Thm_GlobalTheory_ReducedAdjoinRootSeparable_isReduced_adjoinRoot_of_separable
-- name    : GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:59.604315+00:00
-- url     : https://prove2.me/theorems/8860223c-811d-49f0-87de-3d964b7dd987
-- title:
--   Reduced Adjoin Root Separable: is Reduced adjoin Root of separable
-- statement:
--   The Reduced Adjoin Root Separable construction uses the is Reduced adjoin Root of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsReducedAdjoinRootOfSeparable.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsReducedAdjoinRootOfSeparable.lean#L5-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ReducedAdjoinRootSeparable

theorem GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : Polynomial k}
    (hf : f.Separable) : IsReduced (AdjoinRoot f) := by sorry
