-- Prove2me | Theorems.Thm_GlobalTheory_UpqTopology_isClosedEmbedding_mat
-- name    : GlobalTheory.UpqTopology.isClosedEmbedding_mat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:19:49.218213+00:00
-- url     : https://prove2.me/theorems/dd9f00be-62ee-4f63-a25c-303fbe04b220
-- title:
--   Upq Topology: is Closed Embedding mat
-- statement:
--   The Upq Topology construction uses the is Closed Embedding mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L51-L55

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.UpqTopology
variable {P Q : ℕ}

theorem GlobalTheory.UpqTopology.isClosedEmbedding_mat : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by sorry
