-- Prove2me | Theorems.Thm_GlobalTheory_T_compact_covered_by_open_cosets
-- name    : GlobalTheory.T.compact_covered_by_open_cosets
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:30:16.580795+00:00
-- url     : https://prove2.me/theorems/05029406-b8c7-416c-a271-defdddbcc88a
-- title:
--   T: compact covered by open cosets
-- statement:
--   The T construction uses the compact covered by open cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CompactCoveredByOpenCosetsStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CompactCoveredByOpenCosetsStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosets
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosetsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.compact_covered_by_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by sorry
