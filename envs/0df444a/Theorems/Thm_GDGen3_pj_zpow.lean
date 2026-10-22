-- Prove2me | Theorems.Thm_GDGen3_pj_zpow
-- name    : GDGen3.pj_zpow
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:15:25.585627+00:00
-- url     : https://prove2.me/theorems/808b4157-d498-4626-868d-6793b4393066
-- title:
--   General-N certificate lemma: pj_zpow
-- statement:
--   Lemma `pj_zpow` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma pj_zpow (r : ℝ) (hr : r ≠ 0) (N : ℕ) :
    2 * pj r N = r ^ (-(2 * (N : ℤ))) - 1 := by sorry
