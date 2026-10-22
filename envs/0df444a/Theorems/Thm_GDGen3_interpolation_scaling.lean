-- Prove2me | Theorems.Thm_GDGen3_interpolation_scaling
-- name    : GDGen3.interpolation_scaling
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:43:48.124197+00:00
-- url     : https://prove2.me/theorems/b71db71b-0e3f-4b5d-be35-f33ca86595b3
-- title:
--   General-N certificate lemma: interpolation_scaling
-- statement:
--   Lemma `interpolation_scaling` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma interpolation_scaling (a s h : ℝ) (he : h = s * a) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (i j : ℕ) :
    Qv a (fun k => s * f k) (fun k l => s ^ 2 * P k l) i j =
      s * Qv h f P i j + s * (1 - s) / 2 * (P i i + P j j - 2 * P i j) := by sorry
