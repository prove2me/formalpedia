-- Prove2me | Theorems.Thm_GlobalTheory_UpqTopology_range_mat
-- name    : GlobalTheory.UpqTopology.range_mat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:20:28.781255+00:00
-- url     : https://prove2.me/theorems/a4494321-3bd5-47ff-8bec-284f930997a7
-- title:
--   Upq Topology: range mat
-- statement:
--   The Upq Topology construction uses the range mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqLocallyCompactGroup.lean#L25-L33

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

theorem GlobalTheory.UpqTopology.range_mat : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {u | uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q} := by sorry
