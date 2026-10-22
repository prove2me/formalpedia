-- Prove2me | Theorems.Thm_GDGen3_pow_slope_strictMono
-- name    : GDGen3.pow_slope_strictMono
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:18:43.329509+00:00
-- url     : https://prove2.me/theorems/afd6349c-4fbe-4d8c-9607-e41c6671b38c
-- title:
--   General-N certificate lemma: pow_slope_strictMono
-- statement:
--   Lemma `pow_slope_strictMono` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma pow_slope_strictMono (z : ℝ) (hz : 1 < z) :
    StrictMono (fun n : ℕ => (z ^ (n + 1) - 1) / ((n : ℝ) + 1)) := by sorry
