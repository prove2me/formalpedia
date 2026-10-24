-- Prove2me | Theorems.Thm_OAI_PiExponent_logJetSurjective_truncatedLogMatrix
-- name    : OAI.PiExponent.logJetSurjective_truncatedLogMatrix
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:34:12.573424+00:00
-- url     : https://prove2.me/theorems/d62b4264-4236-4c14-bf3a-de0d97ce32ab
-- title:
--   Logarithmic jet surjectivity gives the matrix with the same cutoff
-- statement:
--   At a fixed natural height, logarithmic jet surjectivity implies surjectivity of the interpolation matrix using exactly the same height-dependent truncation. Prove it by monomial expansion and coefficient identification. Input degrees remain ≤ H and output degrees remain strictly < H; H = 0 and zero transverse dimension are included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open scoped BigOperators

theorem OAI.PiExponent.logJetSurjective_truncatedLogMatrix
    (m K : ℕ) (w0 v0 theta : ℚ) (w : Fin m → ℕ)
    (r : Fin m → ℂ) (H : ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hjet : OAI.PiExponent.logJetSurjective m K w0 v0 theta w
      (fun j i => (j.val : ℂ) * r i) H) :
    Function.Surjective
      (OAI.PiExponent.InterpolationMatrix.truncatedLogMatrix K
        (w0 : ℝ) (v0 : ℝ) (theta : ℝ) (fun i => (w i : ℝ)) (H : ℝ) r
        (fun _ => Nat.ceil ((H : ℝ) / (v0 : ℝ)))).mulVecLin := by sorry
