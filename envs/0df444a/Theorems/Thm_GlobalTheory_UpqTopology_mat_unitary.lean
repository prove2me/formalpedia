-- Prove2me | Theorems.Thm_GlobalTheory_UpqTopology_mat_unitary
-- name    : GlobalTheory.UpqTopology.mat_unitary
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:20:13.503497+00:00
-- url     : https://prove2.me/theorems/cb316061-d06b-43ff-aaf2-1b0e53637871
-- title:
--   Upq Topology: mat unitary
-- statement:
--   The Upq Topology construction uses the mat unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L20-L20

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

theorem GlobalTheory.UpqTopology.mat_unitary (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := by sorry
