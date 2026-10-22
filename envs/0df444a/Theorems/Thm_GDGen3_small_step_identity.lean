-- Prove2me | Theorems.Thm_GDGen3_small_step_identity
-- name    : GDGen3.small_step_identity
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:47:29.558504+00:00
-- url     : https://prove2.me/theorems/3bb27fdf-3108-4e06-82a6-7e7a0234d605
-- title:
--   General-N certificate lemma: small_step_identity
-- statement:
--   Lemma `small_step_identity` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma small_step_identity (N : ℕ) (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ)
    (X0 XN : ℝ) (hP : ∀ i j, P i j = P j i)
    (htrajectory : XN = X0 - 2 * h * (∑ i ∈ range N, R i)
      + h ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j)) :
    h * smallK N h f (fun i => P i i)
      + 2 * h * (∑ i ∈ range N, (-f i + gself h R P i - (1 / 2) * P i i)) =
      X0 - XN - 2 * (N : ℝ) * h * f N - (N : ℝ) * h * (1 + (N : ℝ) * h) * P N N := by sorry
