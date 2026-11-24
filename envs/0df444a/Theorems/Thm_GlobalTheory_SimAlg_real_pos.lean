-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_real_pos
-- name    : GlobalTheory.SimAlg.real_pos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:12:19.112891+00:00
-- url     : https://prove2.me/theorems/9d49e36c-016c-4c88-a0ab-4f3315f02eba
-- title:
--   Sim Alg: real pos
-- statement:
--   The Sim Alg construction uses the real pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L74-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg

theorem GlobalTheory.SimAlg.real_pos {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ) (hs : ∀ i j, G i j = G j i)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℝ)
    (hx : ∑ i, ∑ j, x i * x j * (G i j : ℝ) = 0) : x = 0 := by sorry
