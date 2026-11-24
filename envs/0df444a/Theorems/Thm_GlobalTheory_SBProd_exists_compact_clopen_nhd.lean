-- Prove2me | Theorems.Thm_GlobalTheory_SBProd_exists_compact_clopen_nhd
-- name    : GlobalTheory.SBProd.exists_compact_clopen_nhd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:20.848543+00:00
-- url     : https://prove2.me/theorems/9479875b-056f-4a18-9c42-c10bd9a0667d
-- title:
--   SBProd: exists compact clopen nhd
-- statement:
--   The SBProd construction uses the exists compact clopen nhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecomposition.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecomposition.lean#L11-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.SBProd

theorem GlobalTheory.SBProd.exists_compact_clopen_nhd {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] {x : H} {U : Set H} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set H, IsClopen V ∧ IsCompact V ∧ x ∈ V ∧ V ⊆ U := by sorry
