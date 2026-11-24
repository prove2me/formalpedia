-- Prove2me | Theorems.Thm_GlobalTheory_DimDrop_finite_of_topologicalKrullDim_nonpos
-- name    : GlobalTheory.DimDrop.finite_of_topologicalKrullDim_nonpos
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:55.612586+00:00
-- url     : https://prove2.me/theorems/09ea16cd-0bf0-4255-a0d6-a0330bc7e152
-- title:
--   Dim Drop: finite of topological Krull Dim nonpos
-- statement:
--   The Dim Drop construction uses the finite of topological Krull Dim nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZero.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZero.lean#L71-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace Order
open GlobalTheory GlobalTheory.DimDrop

theorem GlobalTheory.DimDrop.finite_of_topologicalKrullDim_nonpos (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    [T0Space S] (h : topologicalKrullDim S ≤ 0) : Finite S := by sorry
