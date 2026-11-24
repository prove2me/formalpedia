-- Prove2me | Theorems.Thm_GlobalTheory_LineThrough_eval_one_lineMap
-- name    : GlobalTheory.LineThrough.eval_one_lineMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:11:32.695925+00:00
-- url     : https://prove2.me/theorems/9ab9058b-da31-4dfd-940d-118a0d5476d3
-- title:
--   Line Through: eval one line Map
-- statement:
--   The Line Through construction uses the eval one line Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L38-L43

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

theorem GlobalTheory.LineThrough.eval_one_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 1 = MvPolynomial.eval c f := by sorry
