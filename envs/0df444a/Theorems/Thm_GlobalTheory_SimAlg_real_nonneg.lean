-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_real_nonneg
-- name    : GlobalTheory.SimAlg.real_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:34.599032+00:00
-- url     : https://prove2.me/theorems/d345d46b-51f8-4a10-913d-86822682cc1d
-- title:
--   Sim Alg: real nonneg
-- statement:
--   The Sim Alg construction uses the real nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L40-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L40-L72

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

theorem GlobalTheory.SimAlg.real_nonneg {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * (G i j : ℝ) := by sorry
