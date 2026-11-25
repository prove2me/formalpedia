-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SplitPlaceUnitaryEvaluation_SplitRepresentatives_cm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation.SplitRepresentatives.cm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:31.638122+00:00
-- url     : https://prove2.me/theorems/6c7dbc1b-72d2-4c01-b9f6-943bf20f871b
-- title:
--   Split Representatives: cm
-- statement:
--   The Split Representatives construction uses the cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/SupportedAtSplit.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/SupportedAtSplit.lean#L82-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct

theorem GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation.SplitRepresentatives.cm (H : SplitRepresentatives) : SplitRepresentativesCM := by sorry
