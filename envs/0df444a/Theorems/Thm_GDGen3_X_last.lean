-- Prove2me | Theorems.Thm_GDGen3_X_last
-- name    : GDGen3.X_last
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:21:22.160253+00:00
-- url     : https://prove2.me/theorems/206b3c0f-769f-4d88-941b-7793f7dd5a3f
-- title:
--   General-N certificate lemma: X_last
-- statement:
--   Lemma `X_last` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma X_last (r : ℝ) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N) : X r N N = 0 := by sorry
