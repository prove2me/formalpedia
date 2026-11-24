-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_WordBlockPolynomials_wordDeriv_perm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.wordDeriv_perm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:52.056573+00:00
-- url     : https://prove2.me/theorems/13c5cf7e-994b-4a84-a695-7b8d4c6e6bae
-- title:
--   Word Block Polynomials: word Deriv perm
-- statement:
--   The Word Block Polynomials construction uses the word Deriv perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/WordDerivativeBlocks.lean#L106-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/WordDerivativeBlocks.lean#L106-L141

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
variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.wordDeriv_perm (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {l l' : List Λ} (h : l.Perm l') : wordDeriv dir l F p = wordDeriv dir l' F p := by sorry
