-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PerpendicularEmbedding_herm_eq_hform
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_eq_hform
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:50.691481+00:00
-- url     : https://prove2.me/theorems/f420aa18-731b-45ca-824f-b907263c7427
-- title:
--   Perpendicular Embedding: herm eq hform
-- statement:
--   The Perpendicular Embedding construction uses the herm eq hform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/PerpendicularEmbedding.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/PerpendicularEmbedding.lean#L30-L35

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_eq_hform {P Q : ℕ} (x y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm x y = _root_.Formalism.UG.hform (starRingEnd ℂ) (_root_.Formalism.UG.Jpq P Q) y x := by sorry
