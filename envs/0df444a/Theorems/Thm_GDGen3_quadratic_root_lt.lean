-- Prove2me | Theorems.Thm_GDGen3_quadratic_root_lt
-- name    : GDGen3.quadratic_root_lt
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:34:59.479203+00:00
-- url     : https://prove2.me/theorems/1fb03032-dac3-4dcb-bf22-a796ee4b4a94
-- title:
--   General-N certificate lemma: quadratic_root_lt
-- statement:
--   Lemma `quadratic_root_lt` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma quadratic_root_lt (p b X x y : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hx : 0 < x) (hy : 0 ≤ y)
    (hroot : p * x ^ 2 + b * x - X = 0) (hq : 0 < p * y ^ 2 + b * y - X) : x < y := by sorry
