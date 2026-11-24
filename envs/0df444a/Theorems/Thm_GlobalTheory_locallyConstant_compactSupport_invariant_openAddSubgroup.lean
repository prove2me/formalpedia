-- Prove2me | Theorems.Thm_GlobalTheory_locallyConstant_compactSupport_invariant_openAddSubgroup
-- name    : GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:17.447798+00:00
-- url     : https://prove2.me/theorems/20ae7c20-bb46-44be-8389-633245956460
-- title:
--   Global Theory: locally Constant compact Support invariant open Add Subgroup
-- statement:
--   The Global Theory construction uses the locally Constant compact Support invariant open Add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyConstantCompactSupportInvariantOpenAddSub.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyConstantCompactSupportInvariantOpenAddSub.lean#L7-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyConstantCompactSupportInvariantOpenAddSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology

theorem GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup :
    ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
      [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g →
      ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by sorry
