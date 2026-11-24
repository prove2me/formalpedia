-- Prove2me | Theorems.Thm_GlobalTheory_UpqTopology_isInducing_mat
-- name    : GlobalTheory.UpqTopology.isInducing_mat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:37:08.065014+00:00
-- url     : https://prove2.me/theorems/821bcd6c-8a7a-4e67-8ab4-fcf2e664b368
-- title:
--   Upq Topology: is Inducing mat
-- statement:
--   The Upq Topology construction uses the is Inducing mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L35-L49

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

theorem GlobalTheory.UpqTopology.isInducing_mat : IsInducing (UpqT.mat (P := P) (Q := Q)) := by sorry
