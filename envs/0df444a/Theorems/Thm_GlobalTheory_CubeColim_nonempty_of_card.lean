-- Prove2me | Theorems.Thm_GlobalTheory_CubeColim_nonempty_of_card
-- name    : GlobalTheory.CubeColim.nonempty_of_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:40.170946+00:00
-- url     : https://prove2.me/theorems/9fdadd91-10b4-41b5-8f52-6762b570d859
-- title:
--   Cube Colim: nonempty of card
-- statement:
--   The Cube Colim construction uses the nonempty of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechComplexDirectLimit.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechComplexDirectLimit.lean#L20-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem GlobalTheory.CubeColim.nonempty_of_card {m : ℕ} (hm : 0 < m) (s : {s : Finset ι // s.card = m}) :
    s.1.Nonempty := by sorry
