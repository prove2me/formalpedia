-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_WordBlockPolynomials_Params_jetBound_pos
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Params.jetBound_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:08.555876+00:00
-- url     : https://prove2.me/theorems/7c534a32-14f4-597e-9613-09d2b1d535a8
-- title:
--   Params: jet Bound pos
-- statement:
--   The Params construction uses the jet Bound pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/WordDerivativeBlocks.lean#L317-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/WordDerivativeBlocks.lean#L317-L323

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Params
variable {f r : ℕ} {rd : ℝ} {D : ℕ} (P : Params dim f r rd D n)

theorem GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Params.jetBound_pos (la : Set.Ioi (0 : ℝ)) : 0 < P.jetBound la := by sorry
