-- Prove2me | Theorems.Thm_GlobalTheory_UpqExpChart_mat_unitary
-- name    : GlobalTheory.UpqExpChart.mat_unitary
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:25:39.525016+00:00
-- url     : https://prove2.me/theorems/1d54e504-e178-4db1-a316-a7d9a7a02b55
-- title:
--   Upq Exp Chart: mat unitary
-- statement:
--   The Upq Exp Chart construction uses the mat unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean#L80-L81

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
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
noncomputable section
open GlobalTheory GlobalTheory.UpqExpChart

theorem GlobalTheory.UpqExpChart.mat_unitary {P Q : ℕ} (g : UpqT P Q) :
    (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := by sorry
