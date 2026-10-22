-- Prove2me | Theorems.Thm_GDGen3_gradient_square_step
-- name    : GDGen3.gradient_square_step
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:45:47.073112+00:00
-- url     : https://prove2.me/theorems/540a5e41-40fd-453d-9da5-7d633b8b48a0
-- title:
--   General-N certificate lemma: gradient_square_step
-- statement:
--   Lemma `gradient_square_step` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma gradient_square_step (h : ℝ) (hh : 0 < h) (hh2 : h ≤ 2)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) (i : ℕ)
    (hQf : 0 ≤ Qv h f P i (i + 1)) (hQb : 0 ≤ Qv h f P (i + 1) i)
    (hdiff : 0 ≤ P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) :
    P (i + 1) (i + 1) ≤ P i i := by sorry
