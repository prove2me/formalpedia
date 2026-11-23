-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_gram_pos
-- name    : GlobalTheory.SimAlg.gram_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:42.635311+00:00
-- url     : https://prove2.me/theorems/829d66d2-ffc3-4c27-88ac-3477ffe765ca
-- title:
--   Sim Alg: gram pos
-- statement:
--   The Sim Alg construction uses the gram pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L110-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L110-L129

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

theorem GlobalTheory.SimAlg.gram_pos {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (hb : ∀ x, x ≠ 0 → 0 < b x x) (φ : Module.End ℤ Λ) (e : Λ) (d : ℕ)
    (hd : ∀ P : ℤ[X], P ≠ 0 → P.degree < d → aeval φ P e ≠ 0) (c : Fin d → ℤ) (hc : c ≠ 0) :
    0 < c ⬝ᵥ (Matrix.of fun i j : Fin d => b ((φ ^ (i : ℕ)) e) ((φ ^ (j : ℕ)) e)) *ᵥ c := by sorry
