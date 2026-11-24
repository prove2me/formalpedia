-- Prove2me | Theorems.Thm_GlobalTheory_CharDotKill_exists_open_ker
-- name    : GlobalTheory.CharDotKill.exists_open_ker
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:03.597803+00:00
-- url     : https://prove2.me/theorems/c633621f-bf7d-49a2-b67d-fe8559f5c8a8
-- title:
--   Char Dot Kill: exists open ker
-- statement:
--   The Char Dot Kill construction uses the exists open ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSubgroupAddCharDotProductTrivialOnCompact.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSubgroupAddCharDotProductTrivialOnCompact.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CharDotKill

theorem GlobalTheory.CharDotKill.exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : ∃ U : OpenAddSubgroup K, ∀ t ∈ U, ψ t = 1 := by sorry
