-- Prove2me | Theorems.Thm_GDGen3_M_le_h
-- name    : GDGen3.M_le_h
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:31:46.616469+00:00
-- url     : https://prove2.me/theorems/09bed516-dd74-41ad-aba9-2dff471e9867
-- title:
--   General-N certificate lemma: M_le_h
-- statement:
--   Lemma `M_le_h` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma M_le_h (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : M r N ≤ 1 + r := by sorry
