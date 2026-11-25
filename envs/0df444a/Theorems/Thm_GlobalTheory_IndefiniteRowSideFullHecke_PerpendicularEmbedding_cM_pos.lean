-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PerpendicularEmbedding_cM_pos
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM_pos
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:14.443096+00:00
-- url     : https://prove2.me/theorems/33bcbceb-5182-5321-8ef5-92b2ad213215
-- title:
--   Perpendicular Embedding: c M pos
-- statement:
--   The Perpendicular Embedding construction uses the c M pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/PerpendicularEmbedding.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/PerpendicularEmbedding.lean#L43-L45

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
open MeasureTheory Matrix
open scoped ENNReal

theorem GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM_pos (M : ℕ) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM M := by sorry
