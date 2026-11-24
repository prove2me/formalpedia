-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_compact_openAddSubgroup
-- name    : GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:45.297557+00:00
-- url     : https://prove2.me/theorems/5677ff5e-3ef2-4782-b111-260ecf68548c
-- title:
--   Haar Uniq: exists compact open Add Subgroup
-- statement:
--   The Haar Uniq construction uses the exists compact open Add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L13-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

theorem GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] :
    ∃ K : OpenAddSubgroup V, IsCompact (K : Set V) := by sorry
