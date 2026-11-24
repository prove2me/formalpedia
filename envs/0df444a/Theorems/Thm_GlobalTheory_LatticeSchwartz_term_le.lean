-- Prove2me | Theorems.Thm_GlobalTheory_LatticeSchwartz_term_le
-- name    : GlobalTheory.LatticeSchwartz.term_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:25.724731+00:00
-- url     : https://prove2.me/theorems/518e3f56-288b-4e49-a8e3-adc71948df9f
-- title:
--   Lattice Schwartz: term le
-- statement:
--   The Lattice Schwartz construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeShiftedCutoffSummable.lean#L23-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeShiftedCutoffSummable.lean#L23-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeShiftedCutoffSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeSchwartz

theorem GlobalTheory.LatticeSchwartz.term_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h f : SchwartzMap V ℂ) (k N j m : ℕ) (x l : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ m f (x - l)‖ ≤
      (2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, m)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
      ((1 + ‖l‖)⁻¹) ^ N := by sorry
