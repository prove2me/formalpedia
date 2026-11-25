-- Prove2me | Theorems.Thm_GlobalTheory_HaarDensityUpq_mat_mul
-- name    : GlobalTheory.HaarDensityUpq.mat_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:20.854417+00:00
-- url     : https://prove2.me/theorems/9e3aa1a2-7fa7-4674-aad3-7e68a44f4817
-- title:
--   Haar Density Upq: mat mul
-- statement:
--   The Haar Density Upq construction uses the mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HaarUpqHasOmegaDensity.lean#L38-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HaarUpqHasOmegaDensity.lean#L38-L38

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsOmegaLebesgueMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HaarUpqHasOmegaDensity
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_ExpBallSandwich_mat_mul

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
open GlobalTheory GlobalTheory.HaarDensityUpq

theorem GlobalTheory.HaarDensityUpq.mat_mul {P Q : ℕ} (g h : UpqT P Q) : (g * h).mat = g.mat * h.mat := by sorry
