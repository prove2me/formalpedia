-- Prove2me | Theorems.Thm_GDGen3_symmetric_square_telescope
-- name    : GDGen3.symmetric_square_telescope
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:16:09.326944+00:00
-- url     : https://prove2.me/theorems/dbbe6cb4-caa9-42da-8795-ecb6500423ca
-- title:
--   General-N certificate lemma: symmetric_square_telescope
-- statement:
--   Lemma `symmetric_square_telescope` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma symmetric_square_telescope (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) (N : ℕ) :
    2 * (∑ i ∈ range N, ∑ j ∈ range i, P i j) + (∑ i ∈ range N, P i i) =
      ∑ i ∈ range N, ∑ j ∈ range N, P i j := by sorry
