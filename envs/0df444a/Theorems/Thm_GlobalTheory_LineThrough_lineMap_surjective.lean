-- Prove2me | Theorems.Thm_GlobalTheory_LineThrough_lineMap_surjective
-- name    : GlobalTheory.LineThrough.lineMap_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:10:52.042331+00:00
-- url     : https://prove2.me/theorems/36285b02-eb51-410d-afd4-d83eee93e45f
-- title:
--   Line Through: line Map surjective
-- statement:
--   The Line Through construction uses the line Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L52-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough

theorem GlobalTheory.LineThrough.lineMap_surjective {d : ℕ} {a c : Fin d → ℂ} (h : c ≠ a) :
    Function.Surjective (lineMap a c) := by sorry
