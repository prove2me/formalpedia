-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_HaarUniq_indicator_mem
-- name    : GlobalTheory.WeilM.HaarUniq.indicator_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:57.699665+00:00
-- url     : https://prove2.me/theorems/b1950abf-fd1e-4e54-be12-3fec3f0d6ea8
-- title:
--   Haar Uniq: indicator mem
-- statement:
--   The Haar Uniq construction uses the indicator mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L23-L33

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

theorem GlobalTheory.WeilM.HaarUniq.indicator_mem [IsTopologicalAddGroup V] [T2Space V]
    (K : OpenAddSubgroup V) (hK : IsCompact (K : Set V)) :
    Set.indicator (K : Set V) (fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.WeilM.SB V := by sorry
