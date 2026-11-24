-- Prove2me | Theorems.Thm_GlobalTheory_compactSpace_UpqT_definite
-- name    : GlobalTheory.compactSpace_UpqT_definite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:45.869184+00:00
-- url     : https://prove2.me/theorems/1702e221-3b6c-47ca-8e63-eac7e9a54779
-- title:
--   Global Theory: compact Space Upq T definite
-- statement:
--   The Global Theory construction uses the compact Space Upq T definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqDefiniteCompact.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqDefiniteCompact.lean#L28-L33

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqDefiniteCompact
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory

theorem GlobalTheory.compactSpace_UpqT_definite :
    ∀ N : ℕ, CompactSpace (UpqT N 0) ∧ CompactSpace (UpqT 0 N) := by sorry
